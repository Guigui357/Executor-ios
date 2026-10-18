// libRbxHook.c — Roblox Luau hook for iOS (arm64, non-jailbroken, Dobby)
// Build:
//   xcrun -sdk iphoneos clang -arch arm64 -dynamiclib \
//       -o libRbxHook.dylib libRbxHook.c \
//       -framework Foundation -framework UIKit \
//       -fobjc-arc -mios-version-min=15.0 \
//       -I Dobby/include -L Dobby -lDobby
//
// Sign with your enterprise cert, inject via NexStore, run.

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
#include <mach/mach.h>
#include <mach-o/dyld.h>
#include <mach-o/loader.h>
#include <mach-o/nlist.h>
#include <mach-o/fat.h>
#include <dlfcn.h>
#include <errno.h>

#include <Foundation/Foundation.h>
#include <UIKit/UIKit.h>

// Dobby — inline hook
#include "dobby.h"

// ---------------------------------------------------------------------------
// Config
// ---------------------------------------------------------------------------
#define HOOK_PORT      47823
#define MAX_PAYLOAD    (1 << 20)
#define MAX_LOG        4096

// ---------------------------------------------------------------------------
// Globals
// ---------------------------------------------------------------------------
static int  g_srv        = -1;
static char g_script_buf[MAX_PAYLOAD + 1];
static char g_log_buf[MAX_LOG];

static void *g_lua_state      = NULL;
static void *g_lua_pcall      = NULL;
static void *g_lua_loadbuffer = NULL;

static FILE *g_log = NULL;

// Original function pointers filled by Dobby
typedef int (*lua_pcall_t)(void *L, int nargs, int nresults, int errfunc);
typedef int (*lua_loadbuffer_t)(void *L, const char *buf, size_t sz, const char *name);

static lua_pcall_t      orig_lua_pcall      = NULL;
static lua_loadbuffer_t orig_lua_loadbuffer = NULL;

// ---------------------------------------------------------------------------
// Logging
// ---------------------------------------------------------------------------
static void logmsg(const char *fmt, ...) {
    va_list ap;
    char buf[1024];

    va_start(ap, fmt);
    vsnprintf(buf, sizeof buf, fmt, ap);
    va_end(ap);

    fprintf(stderr, "[RbxHook] %s\n", buf);
    fflush(stderr);

    if (!g_log) g_log = fopen("/tmp/rbxhook.log", "a");
    if (g_log) {
        fprintf(g_log, "[RbxHook] %s\n", buf);
        fflush(g_log);
    }
}

// ---------------------------------------------------------------------------
// Symbol lookup via dyld image iteration (works on stripped binaries)
// ---------------------------------------------------------------------------
static void *find_symbol_in_image(const struct mach_header_64 *hdr,
                                  const char *target) {
    const struct segment_command_64 *linkedit = NULL;
    const struct segment_command_64 *text = NULL;
    const struct symtab_command *symtab = NULL;

    uintptr_t base = (uintptr_t)hdr;
    const uint8_t *p = (const uint8_t *)hdr + sizeof(struct mach_header_64);

    for (uint32_t i = 0; i < hdr->ncmds; i++) {
        const struct load_command *lc = (const struct load_command *)p;
        switch (lc->cmd) {
        case LC_SEGMENT_64: {
            const struct segment_command_64 *seg = (const struct segment_command_64 *)lc;
            if (strncmp(seg->segname, "__LINKEDIT", 10) == 0) linkedit = seg;
            if (strncmp(seg->segname, "__TEXT", 6) == 0) text = seg;
            break;
        }
        case LC_SYMTAB:
            symtab = (const struct symtab_command *)lc;
            break;
        }
        p += lc->cmdsize;
    }

    if (!symtab || !linkedit || !text) return NULL;

    intptr_t slide = _dyld_get_image_vmaddr_slide((uint32_t)((uintptr_t)hdr - (uintptr_t)_dyld_get_image_header(0)));
    // Use global slide instead of per-image for simplicity
    slide = _dyld_get_image_vmaddr_slide(0);

    const char *strtab = (const char *)(base + symtab->stroff);
    const struct nlist_64 *syms = (const struct nlist_64 *)(base + symtab->symoff);

    for (uint32_t i = 0; i < symtab->nsyms; i++) {
        if (syms[i].n_un.n_strx == 0) continue;
        if (syms[i].n_value == 0) continue;
        const char *name = strtab + syms[i].n_un.n_strx;
        if (strcmp(name, target) == 0) {
            // n_value is vmaddr; add slide for runtime address
            return (void *)(base + syms[i].n_value - (uintptr_t)hdr + (uintptr_t)hdr);
        }
    }
    return NULL;
}

static void *find_any_symbol(const char *name) {
    uint32_t count = _dyld_image_count();
    for (uint32_t i = 0; i < count; i++) {
        const struct mach_header_64 *hdr = (const struct mach_header_64 *)_dyld_get_image_header(i);
        if (!hdr || hdr->magic != MH_MAGIC_64) continue;
        void *found = find_symbol_in_image(hdr, name);
        if (found) {
            logmsg("symbol %s @ %p (image %u)", name, found, i);
            return found;
        }
    }
    return NULL;
}

// ---------------------------------------------------------------------------
// Prologue scan for lua_pcall / luaL_loadbuffer in __TEXT of every image
// ---------------------------------------------------------------------------
static void *scan_text_for_sig(const uint8_t *sig, size_t sig_len,
                               const char **out_image) {
    uint32_t count = _dyld_image_count();
    for (uint32_t i = 0; i < count; i++) {
        const struct mach_header_64 *hdr = (const struct mach_header_64 *)_dyld_get_image_header(i);
        if (!hdr || hdr->magic != MH_MAGIC_64) continue;
        const uint8_t *p = (const uint8_t *)hdr + sizeof(struct mach_header_64);
        for (uint32_t j = 0; j < hdr->ncmds; j++) {
            const struct load_command *lc = (const struct load_command *)p;
            if (lc->cmd == LC_SEGMENT_64) {
                const struct segment_command_64 *seg = (const struct segment_command_64 *)lc;
                if (strncmp(seg->segname, "__TEXT", 6) == 0) {
                    const uint8_t *text = (const uint8_t *)hdr + seg->vmaddr;
                    const uint8_t *text_end = text + seg->filesize;
                    for (const uint8_t *q = text; q + sig_len < text_end; q++) {
                        if (((uintptr_t)q & 3) != 0) continue;
                        if (memcmp(q, sig, sig_len) == 0) {
                            if (out_image) *out_image = _dyld_get_image_name(i);
                            return (void *)q;
                        }
                    }
                }
            }
            p += lc->cmdsize;
        }
    }
    return NULL;
}

// luaL_loadbuffer prologue: stp x29,x30,[sp,#-0x30]!; str x21,[sp,#0x10]; stp x20,x19,[sp,#0x20]; mov x29,sp
static const uint8_t SIG_LOADBUF[] = {
    0xFD,0x7B,0xBD,0xA9, 0xF5,0x0B,0x00,0xF9,
    0xF4,0x4F,0x02,0xA9, 0xFD,0x03,0x00,0x91,
};

// lua_pcall prologue: stp x29,x30,[sp,#-0x20]!; stp x20,x19,[sp,#0x10]; mov x29,sp; mov x19,x0
static const uint8_t SIG_PCALL[] = {
    0xFD,0x7B,0xBE,0xA9, 0xF4,0x4F,0x01,0xA9,
    0xFD,0x03,0x00,0x91, 0xF3,0x03,0x00,0xAA,
};

// ---------------------------------------------------------------------------
// Hook implementations
// ---------------------------------------------------------------------------
static int my_lua_pcall(void *L, int nargs, int nresults, int errfunc) {
    if (!g_lua_state && L) {
        g_lua_state = L;
        logmsg("captured lua_State @ %p (from pcall)", L);
    }
    return orig_lua_pcall ? orig_lua_pcall(L, nargs, nresults, errfunc) : -1;
}

static int my_luaL_loadbuffer(void *L, const char *buf, size_t sz, const char *name) {
    if (!g_lua_state && L) {
        g_lua_state = L;
        logmsg("captured lua_State @ %p (from loadbuffer)", L);
    }
    return orig_lua_loadbuffer ? orig_lua_loadbuffer(L, buf, sz, name) : -1;
}

static void install_hooks(void) {
    // Try symbols first (rare for Roblox but cheap to check)
    if (!g_lua_pcall) {
        g_lua_pcall = find_any_symbol("lua_pcall");
    }
    if (!g_lua_loadbuffer) {
        g_lua_loadbuffer = find_any_symbol("luaL_loadbuffer");
    }

    // Prologue scan if symbols missing
    if (!g_lua_pcall) {
        const char *img = NULL;
        g_lua_pcall = scan_text_for_sig(SIG_PCALL, sizeof SIG_PCALL, &img);
        if (g_lua_pcall) logmsg("lua_pcall prologue match @ %p in %s", g_lua_pcall, img ? img : "?");
    }
    if (!g_lua_loadbuffer) {
        const char *img = NULL;
        g_lua_loadbuffer = scan_text_for_sig(SIG_LOADBUF, sizeof SIG_LOADBUF, &img);
        if (g_lua_loadbuffer) logmsg("luaL_loadbuffer prologue match @ %p in %s", g_lua_loadbuffer, img ? img : "?");
    }

    // Hook luaL_loadbuffer with Dobby
    if (g_lua_loadbuffer) {
        int r = DobbyHook((void *)g_lua_loadbuffer,
                          (void *)my_luaL_loadbuffer,
                          (void **)&orig_lua_loadbuffer);
        logmsg("DobbyHook loadbuffer @ %p => %d", g_lua_loadbuffer, r);
    }

    // Hook lua_pcall with Dobby
    if (g_lua_pcall) {
        int r = DobbyHook((void *)g_lua_pcall,
                          (void *)my_lua_pcall,
                          (void **)&orig_lua_pcall);
        logmsg("DobbyHook lua_pcall @ %p => %d", g_lua_pcall, r);
    }
}

// ---------------------------------------------------------------------------
// Execute a script through the discovered state
// ---------------------------------------------------------------------------
static int run_script(void *L, const char *src, size_t len, const char *name) {
    if (!L) { logmsg("run_script: no L"); return -1; }
    if (!orig_lua_loadbuffer || !orig_lua_pcall) {
        logmsg("run_script: no funcs (lb=%p pc=%p)", orig_lua_loadbuffer, orig_lua_pcall);
        return -1;
    }
    int r1 = orig_lua_loadbuffer(L, src, len, name ? name : "=rbxexec");
    logmsg("loadbuffer(L=%p) = %d", L, r1);
    if (r1 != 0) return -1;
    int r2 = orig_lua_pcall(L, 0, 0, 0);
    logmsg("pcall(L=%p) = %d", L, r2);
    return r2;
}

// ---------------------------------------------------------------------------
// TCP server
// ---------------------------------------------------------------------------
static int read_line(int fd, char *out, size_t cap) {
    size_t i = 0;
    while (i + 1 < cap) {
        char c;
        ssize_t r = read(fd, &c, 1);
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
    if (g_srv < 0) { logmsg("socket failed: %d", errno); return NULL; }

    int opt = 1;
    setsockopt(g_srv, SOL_SOCKET, SO_REUSEADDR, &opt, sizeof opt);

    struct sockaddr_in addr = {0};
    addr.sin_family      = AF_INET;
    addr.sin_addr.s_addr = htonl(INADDR_LOOPBACK);
    addr.sin_port        = htons(HOOK_PORT);

    if (bind(g_srv, (struct sockaddr *)&addr, sizeof addr) != 0) {
        logmsg("bind failed: %d", errno); close(g_srv); return NULL;
    }
    if (listen(g_srv, 4) != 0) {
        logmsg("listen failed: %d", errno); close(g_srv); return NULL;
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
            ssize_t r = read(cli, g_script_buf + got, n - got);
            if (r <= 0) break;
            got += r;
        }
        g_script_buf[got] = 0;

        if (got != (size_t)n) { write(cli, "E short\n", 8); close(cli); continue; }

        logmsg("received %zu bytes name=%s", got, name);

        if (!g_lua_state) {
            logmsg("no lua_State captured yet — waiting for Roblox to call loadbuffer/pcall");
            write(cli, "E nolua\n", 7);
            close(cli);
            continue;
        }

        int rc = run_script(g_lua_state, g_script_buf, got, name);
        const char *reply = (rc == 0) ? "0 OK\n" : "1 ERR\n";
        write(cli, reply, strlen(reply));
        close(cli);
    }
    return NULL;
}

// ---------------------------------------------------------------------------
// Constructor
// ---------------------------------------------------------------------------
__attribute__((constructor))
static void on_load(void) {
    logmsg("libRbxHook loaded (pid=%d) on arm64", getpid());

    // Enumerate images once for visibility
    uint32_t count = _dyld_image_count();
    for (uint32_t i = 0; i < count; i++) {
        const char *name = _dyld_get_image_name(i);
        if (name && strstr(name, "roblox")) {
            logmsg("image %u: %s", i, name);
        }
    }

    install_hooks();

    logmsg("state=%p pcall=%p loadbuffer=%p originals=(pcall=%p lb=%p)",
           g_lua_state, g_lua_pcall, g_lua_loadbuffer,
           orig_lua_pcall, orig_lua_loadbuffer);

    pthread_t t;
    if (pthread_create(&t, NULL, server_thread, NULL) == 0) {
        pthread_detach(t);
    } else {
        logmsg("pthread_create failed");
    }

    logmsg("hook ready");
}
