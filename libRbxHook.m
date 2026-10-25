// libRbxHook.c — dlsym + heap-scan, no executable-memory patches.
// Build:
//   xcrun -sdk iphoneos clang -arch arm64 -dynamiclib \
//       -o libRbxHook.dylib libRbxHook.c \
//       -framework Foundation -framework UIKit -mios-version-min=15.0 \
//       -fobjc-arc

#include <stdio.h>
#include <stdarg.h>
#include <string.h>
#include <stdlib.h>
#include <unistd.h>
#include <pthread.h>
#include <signal.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <arpa/inet.h>
#include <dlfcn.h>
#include <errno.h>
#include <mach/mach.h>
#include <mach-o/dyld.h>

#include <Foundation/Foundation.h>

#define HOOK_PORT      47823
#define MAX_PAYLOAD    (1 << 20)
#define MAX_CANDIDATES 512

// Lua / Luau types (Luau order differs slightly; these are stable):
#define LUA_TNIL     0
#define LUA_TBOOLEAN 1
#define LUA_TNUMBER  3
#define LUA_TSTRING  4
#define LUA_TTABLE   5

typedef int (*lua_loadbuffer_t)(void *L, const char *buf, size_t sz, const char *name);
typedef int   (*lua_pcall_t)(void *L, int nargs, int nresults, int errfunc);
typedef int   (*lua_gettop_t)(void *L);
typedef void  (*lua_settop_t)(void *L, int idx);
typedef int   (*lua_type_t)(void *L, int idx);
typedef int   (*lua_getglobal_t)(void *L, const char *name);

static lua_loadbuffer_t p_loadbuffer;
static lua_pcall_t      p_pcall;
static lua_gettop_t     p_gettop;
static lua_settop_t     p_settop;
static lua_type_t       p_type;
static lua_getglobal_t  p_getglobal;

static void *g_L = NULL;
static int   g_srv = -1;
static char  g_script[MAX_PAYLOAD + 1];

static void logmsg(const char *fmt, ...) {
    va_list ap; char b[1024];
    va_start(ap, fmt); vsnprintf(b, sizeof b, fmt, ap); va_end(ap);

    // 1. stderr — bypasses os_log privacy entirely. This is the one that shows in idevicesyslog.
    fprintf(stderr, "[RbxHook] %s\n", b);
    fflush(stderr);

    // 2. os_log with explicit public marker — survives Apple's privacy redaction.
    NSLog(@"[RbxHook] %{public}s", b);

    // 3. file fallback — survives everything, including stderr being swallowed.
    static FILE *f = NULL;
    if (!f) f = fopen("/tmp/rbxhook.log", "a");
    if (f) { fprintf(f, "%s\n", b); fflush(f); }
}

static int resolve_symbols(void) {
    p_loadbuffer = (lua_loadbuffer_t)dlsym(RTLD_DEFAULT, "luaL_loadbuffer");
    p_pcall      = (lua_pcall_t)     dlsym(RTLD_DEFAULT, "lua_pcall");
    p_gettop     = (lua_gettop_t)    dlsym(RTLD_DEFAULT, "lua_gettop");
    p_settop     = (lua_settop_t)    dlsym(RTLD_DEFAULT, "lua_settop");
    p_type       = (lua_type_t)      dlsym(RTLD_DEFAULT, "lua_type");
    p_getglobal  = (lua_getglobal_t) dlsym(RTLD_DEFAULT, "lua_getglobal");

    logmsg("sym: lb=%p pc=%p gt=%p st=%p ty=%p gg=%p",
           p_loadbuffer, p_pcall, p_gettop, p_settop, p_type, p_getglobal);

    return (p_loadbuffer && p_pcall && p_gettop && p_settop && p_type && p_getglobal);
}

// --- Heap walk: collect plausible lua_State pointers -------------------------
//
// Luau lua_State layout (simplified, 8.x):
//   offset 0:  uint8_t tt           (tag byte; Luau uses 6 for THREAD-ish)
//   offset 1:  uint8_t marked
//   offset 4:  uint8_t status
//   offset 8:  global_State *l_G   (pointer into another heap region)
//   offset 24: StkId base          (pointer into the thread's stack)
//   offset 32: StkId top
// We do NOT assume exact offsets — we validate by calling lua_gettop().
//
// Strategy: scan all rw- regions for 8-byte values that point into a
// different rw- region (candidate l_G), then test the *container* address
// as a lua_State by calling lua_gettop().
//
// Better strategy: an actual lua_State is the first word of a thread block,
// and Roblox's main state is *persistent* — created once at boot, never freed.
// We can't tell which is main, but we can try candidates in order until one
// has a `game` global of type table.

static int is_readable_addr(vm_address_t a) {
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

static int validate_L(void *L) {
    if (!L) return 0;
    if (!is_readable_addr((vm_address_t)L)) return 0;

    int top;
    // Guard against segfault on bogus candidate — assume readable,
    // but check the top value looks sane before diving in.
    // (Roblox's lua_gettop reads L->top - L->base; if the struct is garbage,
    //  this can crash. We accept that risk; the scan is best-effort.)
    top = p_gettop(L);
    if (top < 0 || top > 100000) return 0;

    // Leave a TValue on the stack, then pop it.
    p_getglobal(L, "game");
    int t = p_type(L, -1);
    p_settop(L, top);           // restore exact pre-call stack depth
    return t == LUA_TTABLE ? 1 : 0;
}

static void scan_for_L(void) {
    if (g_L && validate_L(g_L)) return;

    vm_address_t addr = 0;
    vm_size_t size = 0;
    int tested = 0, found = 0;

    while (tested < MAX_CANDIDATES) {
        vm_region_basic_info_data_64_t info;
        mach_msg_type_number_t cnt = VM_REGION_BASIC_INFO_COUNT_64;
        mach_port_t obj = MACH_PORT_NULL;

        kern_return_t kr = vm_region_64(mach_task_self(), &addr, &size,
                                        VM_REGION_BASIC_INFO_64,
                                        (vm_region_info_t)&info, &cnt, &obj);
        if (obj != MACH_PORT_NULL) mach_port_deallocate(mach_task_self(), obj);
        if (kr != KERN_SUCCESS) break;

        // Only consider writable, non-executable pages.
        int writable = (info.protection & VM_PROT_WRITE);
        int exec     = (info.protection & VM_PROT_EXECUTE);
        if (writable && !exec) {
            uint8_t *p = (uint8_t *)addr;
            for (vm_size_t off = 0; off + 64 < size; off += 8) {
                // The lua_State is 8-aligned. Candidate header at p+off.
                // Cheap pre-check: read the l_G pointer at +8, confirm it's
                // in the same heap class (readable, writable, non-exec).
                uintptr_t cand = (uintptr_t)(p + off);
                uintptr_t g_ptr = *(uintptr_t *)(cand + 8);

                if (!is_readable_addr(g_ptr)) continue;
                if (g_ptr < 0x1000) continue;

                tested++;
                if (validate_L((void *)cand)) {
                    g_L = (void *)cand;
                    logmsg("L found @ %p after %d candidates", g_L, tested);
                    found = 1;
                    break;
                }
                if (tested >= MAX_CANDIDATES) break;
            }
        }
        addr += size;
        if (found) break;
    }

    if (!g_L) logmsg("L not found after %d candidates", tested);
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

static int exec_script(const char *src, size_t len, const char *name) {
    if (!g_L) scan_for_L();
    if (!g_L) return -1;

    int base = p_gettop(g_L);
    int rc = p_loadbuffer(g_L, src, len, name ? name : "=rbxexec");
    logmsg("loadbuffer -> %d", rc);
    if (rc != 0) {
        // error string on top, leave it for caller? just restore depth.
        p_settop(g_L, base);
        return -2;
    }
    rc = p_pcall(g_L, 0, 0, 0);
    logmsg("pcall -> %d", rc);
    p_settop(g_L, base);
    return rc;
}

static void *server_thread(void *arg) {
    (void)arg;
    signal(SIGPIPE, SIG_IGN);

    g_srv = socket(AF_INET, SOCK_STREAM, 0);
    if (g_srv < 0) { logmsg("socket %d", errno); return NULL; }

    int opt = 1;
    setsockopt(g_srv, SOL_SOCKET, SO_REUSEADDR, &opt, sizeof opt);

    struct sockaddr_in a = {0};
    a.sin_family = AF_INET;
    a.sin_addr.s_addr = htonl(INADDR_LOOPBACK);
    a.sin_port = htons(HOOK_PORT);

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
        char nhdr[128];
        if (read_line(cli, nhdr, sizeof nhdr) < 0) { close(cli); continue; }
        char name[128] = "=rbxexec";
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

        if (got != (size_t)n) { write(cli, "E short\n", 8); close(cli); continue; }

        int rc = exec_script(g_script, got, name);
        const char *reply = (rc == 0) ? "0 OK\n" : "1 ERR\n";
        write(cli, reply, strlen(reply));
        close(cli);
    }
    return NULL;
}

__attribute__((constructor))
static void on_load(void) {
    logmsg("libRbxHook loaded (pid=%d)", getpid());

    if (!resolve_symbols()) {
        logmsg("FATAL: Roblox does not export lua_* symbols. dlsym path dead. Jailbreak required.");
        return;
    }

    pthread_t t;
    if (pthread_create(&t, NULL, server_thread, NULL) == 0) pthread_detach(t);
}
