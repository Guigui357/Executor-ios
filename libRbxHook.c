// libRbxHook.c — Roblox Luau executor loader for iOS (arm64, non-JB)
// No executable-memory patches. dlsym + heap scan for lua_State.
//
// Build:
//   xcrun -sdk iphoneos clang -arch arm64 -dynamiclib \
//       -o libRbxHook.dylib libRbxHook.c \
//       -framework Foundation -framework UIKit \
//       -mios-version-min=15.0 -fobjc-arc -O2
//
// Inject via LC_LOAD_DYLIB (insert_dylib / NexStore inject), re-sign, run.

#include <stdio.h>
#include <stdarg.h>
#include <string.h>
#include <stdlib.h>
#include <unistd.h>
#include <pthread.h>
#include <signal.h>
#include <setjmp.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <arpa/inet.h>
#include <dlfcn.h>
#include <errno.h>
#include <mach/mach.h>
#include <mach-o/dyld.h>
#include <malloc/malloc.h>
#include <dispatch/dispatch.h>

#include <Foundation/Foundation.h>

#define HOOK_PORT      47823
#define MAX_PAYLOAD    (1 << 20)
#define MAX_CANDIDATES 200000

#define LUA_TNIL     0
#define LUA_TBOOLEAN 1
#define LUA_TNUMBER  3
#define LUA_TSTRING  4
#define LUA_TTABLE   5

typedef int (*lua_loadbuffer_t)(void *L, const char *buf, size_t sz, const char *name);
typedef int (*lua_loadbufferx_t)(void *L, const char *buf, size_t sz, const char *name, const char *mode);
typedef int (*lua_pcall_t)(void *L, int nargs, int nresults, int errfunc);
typedef int (*lua_pcallk_t)(void *L, int nargs, int nresults, int errfunc, void *ctx, void *k);
typedef int (*lua_gettop_t)(void *L);
typedef void (*lua_settop_t)(void *L, int idx);
typedef int (*lua_type_t)(void *L, int idx);
typedef int (*lua_getglobal_t)(void *L, const char *name);

static lua_loadbuffer_t  p_loadbuffer  = NULL;
static lua_loadbufferx_t p_loadbufferx = NULL;
static lua_pcall_t       p_pcall       = NULL;
static lua_pcallk_t      p_pcallk      = NULL;
static lua_gettop_t      p_gettop      = NULL;
static lua_settop_t      p_settop      = NULL;
static lua_type_t        p_type        = NULL;
static lua_getglobal_t   p_getglobal   = NULL;

static void *g_L       = NULL;
static int   g_srv     = -1;
static char  g_script[MAX_PAYLOAD + 1];

// --- Logging ----------------------------------------------------------------
static void logmsg(const char *fmt, ...) {
    va_list ap; char b[1024];
    va_start(ap, fmt); vsnprintf(b, sizeof b, fmt, ap); va_end(ap);

    fprintf(stderr, "[RbxHook] %s\n", b);
    fflush(stderr);

    static FILE *f = NULL;
    if (!f) f = fopen("/tmp/rbxhook.log", "a");
    if (f) { fprintf(f, "%s\n", b); fflush(f); }
}

// --- Symbol resolution ------------------------------------------------------
static int resolve_symbols(void) {
    p_loadbuffer  = (lua_loadbuffer_t) dlsym(RTLD_DEFAULT, "luaL_loadbuffer");
    p_loadbufferx = (lua_loadbufferx_t)dlsym(RTLD_DEFAULT, "luaL_loadbufferx");
    p_pcall       = (lua_pcall_t)      dlsym(RTLD_DEFAULT, "lua_pcall");
    p_pcallk      = (lua_pcallk_t)     dlsym(RTLD_DEFAULT, "lua_pcallk");
    p_gettop      = (lua_gettop_t)     dlsym(RTLD_DEFAULT, "lua_gettop");
    p_settop      = (lua_settop_t)     dlsym(RTLD_DEFAULT, "lua_settop");
    p_type        = (lua_type_t)       dlsym(RTLD_DEFAULT, "lua_type");
    p_getglobal   = (lua_getglobal_t)  dlsym(RTLD_DEFAULT, "lua_getglobal");

    if (!p_loadbuffer && !p_loadbufferx) return 0;
    if (!p_pcall      && !p_pcallk)      return 0;
    if (!p_gettop || !p_settop || !p_type || !p_getglobal) return 0;

    logmsg("sym: lb=%p lbx=%p pc=%p pck=%p gt=%p st=%p ty=%p gg=%p",
           p_loadbuffer, p_loadbufferx, p_pcall, p_pcallk,
           p_gettop, p_settop, p_type, p_getglobal);
    return 1;
}

// --- Crash-guarded candidate probing ---------------------------------------
static sigjmp_buf          g_scan_jb;
static volatile sig_atomic_t g_in_probe = 0;

static void scan_segv_handler(int sig) {
    (void)sig;
    if (g_in_probe) siglongjmp(g_scan_jb, 1);
    _exit(139);  // real crash outside probe — die clean
}

static int is_readable_addr(vm_address_t a) {
    if (a < 0x1000) return 0;
    vm_size_t sz = 0;
    vm_region_basic_info_data_64_t info;
    mach_msg_type_number_t cnt = VM_REGION_BASIC_INFO_COUNT_64;
    mach_port_t obj = MACH_PORT_NULL;
    kern_return_t kr = vm_region_64(mach_task_self(), &a, &sz,
                                    VM_REGION_BASIC_INFO_64,
                                    (vm_region_info_t)&info, &cnt, &obj);
    if (obj != MACH_PORT_NULL) mach_port_deallocate(mach_task_self(), obj);
    return kr == KERN_SUCCESS;
}

static int ptr_in_malloc_zone(uintptr_t p) {
    return malloc_zone_from_ptr((void *)p) != NULL;
}

static int probe_one_global(void *L, const char *name) {
    p_getglobal(L, name);
    return p_type(L, -1) == LUA_TTABLE;
}

static int validate_L_safe(void *L) {
    if (!L) return 0;
    if (!is_readable_addr((vm_address_t)L)) return 0;

    g_in_probe = 1;
    if (sigsetjmp(g_scan_jb, 1) != 0) {
        g_in_probe = 0;
        return 0;
    }

    int top = p_gettop(L);
    if (top < 0 || top > 100000) { g_in_probe = 0; return 0; }

    int ok = 0;
    if (probe_one_global(L, "game"))       ok = 1;
    else if (probe_one_global(L, "workspace")) ok = 1;

    p_settop(L, top);
    g_in_probe = 0;
    return ok;
}

// --- Heap scan for lua_State ------------------------------------------------
static void scan_for_L(void) {
    if (g_L && validate_L_safe(g_L)) return;
    g_L = NULL;

    vm_address_t addr = 0;
    vm_size_t    size = 0;
    long         tested = 0;

    while (tested < MAX_CANDIDATES) {
        vm_region_basic_info_data_64_t info;
        mach_msg_type_number_t cnt = VM_REGION_BASIC_INFO_COUNT_64;
        mach_port_t obj = MACH_PORT_NULL;

        kern_return_t kr = vm_region_64(mach_task_self(), &addr, &size,
                                        VM_REGION_BASIC_INFO_64,
                                        (vm_region_info_t)&info, &cnt, &obj);
        if (obj != MACH_PORT_NULL) mach_port_deallocate(mach_task_self(), obj);
        if (kr != KERN_SUCCESS) break;

        int writable = (info.protection & VM_PROT_WRITE);
        int exec     = (info.protection & VM_PROT_EXECUTE);

        if (writable && !exec && size <= (256ULL * 1024 * 1024)) {
            uint8_t *p = (uint8_t *)addr;
            for (vm_size_t off = 0; off + 64 < size; off += 8) {
                uintptr_t cand = (uintptr_t)(p + off);
                if (!ptr_in_malloc_zone(cand)) continue;

                uintptr_t g_ptr;
                if (!is_readable_addr((vm_address_t)(cand + 8))) continue;
                g_ptr = *(uintptr_t *)(cand + 8);
                if (g_ptr < 0x1000) continue;
                if (!ptr_in_malloc_zone(g_ptr)) continue;

                tested++;
                if (validate_L_safe((void *)cand)) {
                    g_L = (void *)cand;
                    logmsg("L found @ %p after %ld candidates", g_L, tested);
                    return;
                }
                if (tested >= MAX_CANDIDATES) break;
            }
        }
        addr += size;
    }
    logmsg("L not found after %ld candidates", tested);
}

// --- Exec ---------------------------------------------------------------
static int exec_script(const char *src, size_t len, const char *name) {
    if (!g_L) scan_for_L();
    if (!g_L) return -1;

    const char *chunk = name ? name : "=rbxexec";
    int base = p_gettop(g_L);

    int rc;
    if (p_loadbuffer)
        rc = p_loadbuffer(g_L, src, len, chunk);
    else
        rc = p_loadbufferx(g_L, src, len, chunk, NULL);

    logmsg("loadbuffer -> %d", rc);
    if (rc != 0) { p_settop(g_L, base); return -2; }

    if (p_pcall)
        rc = p_pcall(g_L, 0, 0, 0);
    else
        rc = p_pcallk(g_L, 0, 0, 0, NULL, NULL);

    logmsg("pcall -> %d", rc);
    p_settop(g_L, base);
    return rc;
}

static int exec_script_on_main(const char *src, size_t len, const char *name) {
    if ([NSThread isMainThread])
        return exec_script(src, len, name);

    __block int result = -1;
    dispatch_sync(dispatch_get_main_queue(), ^{
        result = exec_script(src, len, name);
    });
    return result;
}

// --- Server -----------------------------------------------------------------
static int read_line(int fd, char *out, size_t cap) {
    size_t i = 0;
    while (i + 1 < cap) {
        char c; ssize_t r = read(fd, &c, 1);
        if (r <= 0) return -1;
        if (c == '\n') { out[i] = 0; return (int)i; }
        out[i++] = c;
    }
    out[i] = 0;
    return -1;
}

static void *server_thread(void *arg) {
    (void)arg;
    signal(SIGPIPE, SIG_IGN);

    g_srv = socket(AF_INET, SOCK_STREAM, 0);
    if (g_srv < 0) { logmsg("socket %d", errno); return NULL; }

    int opt = 1;
    setsockopt(g_srv, SOL_SOCKET, SO_REUSEADDR, &opt, sizeof opt);

    struct sockaddr_in a = {0};
    a.sin_family      = AF_INET;
    a.sin_addr.s_addr = htonl(INADDR_LOOPBACK);
    a.sin_port        = htons(HOOK_PORT);

    if (bind(g_srv, (struct sockaddr *)&a, sizeof a) != 0) {
        logmsg("bind %d", errno); close(g_srv); return NULL;
    }
    if (listen(g_srv, 4) != 0) {
        logmsg("listen %d", errno); close(g_srv); return NULL;
    }
    logmsg("listening on 127.0.0.1:%d", HOOK_PORT);

    for (;;) {
        int cli = accept(g_srv, NULL, NULL);
        if (cli < 0) continue;

        struct timeval tv = { 15, 0 };
        setsockopt(cli, SOL_SOCKET, SO_RCVTIMEO, &tv, sizeof tv);

        char hdr[256];
        if (read_line(cli, hdr, sizeof hdr) < 0) { close(cli); continue; }
        long n = -1;
        if (sscanf(hdr, "SIZE %ld", &n) != 1 || n < 0 || n > MAX_PAYLOAD) {
            write(cli, "E size\n", 7); close(cli); continue;
        }

        char nhdr[256];
        if (read_line(cli, nhdr, sizeof nhdr) < 0) { close(cli); continue; }
        char name[200] = "=rbxexec";
        if (strncmp(nhdr, "NAME ", 5) == 0) {
            snprintf(name, sizeof name, "%s", nhdr + 5);
            if (name[0] != '=' && name[0] != '@') {
                memmove(name + 1, name, strlen(name) + 1);
                name[0] = '=';
            }
        }

        size_t got = 0;
        while (got < (size_t)n) {
            ssize_t r = read(cli, g_script + got, n - got);
            if (r <= 0) break;
            got += r;
        }
        g_script[got] = 0;

        if (got != (size_t)n) {
            write(cli, "E short\n", 8); close(cli); continue;
        }

        int rc = exec_script_on_main(g_script, got, name);
        const char *reply = (rc == 0) ? "0 OK\n" : "1 ERR\n";
        write(cli, reply, strlen(reply));
        close(cli);
    }
    return NULL;
}

// --- Constructor -------------------------------------------------------------
__attribute__((constructor))
static void on_load(void) {
    logmsg("libRbxHook loaded (pid=%d)", getpid());

    struct sigaction sa = {0};
    sa.sa_handler = scan_segv_handler;
    sigemptyset(&sa.sa_mask);
    sa.sa_flags = SA_NODEFER;
    sigaction(SIGSEGV, &sa, NULL);
    sigaction(SIGBUS,  &sa, NULL);

    if (!resolve_symbols()) {
        logmsg("FATAL: Roblox does not export lua_* symbols. dlsym path dead. Jailbreak required.");
        return;
    }

    pthread_t t;
    if (pthread_create(&t, NULL, server_thread, NULL) == 0) pthread_detach(t);
}
