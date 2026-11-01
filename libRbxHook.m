// libRbxHook.m — iOS dylib with signature scanning
#import <Foundation/Foundation.h>
#import <UIKit/UIKit.h>
#import <mach/mach.h>
#import <mach-o/dyld.h>
#import <mach-o/loader.h>
#import <mach-o/nlist.h>
#import <pthread.h>
#import <signal.h>
#import <sys/socket.h>
#import <netinet/in.h>
#import <arpa/inet.h>
#import <unistd.h>
#import <dlfcn.h>
#import <string.h>

#include "dobby.h"

#define HOOK_PORT   47823
#define MAX_PAYLOAD (1 << 20)

typedef int (*lua_loadbuffer_t)(void *L, const char *buf, size_t sz, const char *name);
typedef int (*lua_pcall_t)(void *L, int nargs, int nresults, int errfunc);

static lua_loadbuffer_t g_lb_orig = NULL;
static lua_pcall_t      g_pc_orig = NULL;
static void *g_L = NULL;
static int   g_srv = -1;
static char  g_script[MAX_PAYLOAD + 1];

// --- Signatures (ARM64) ---
// luaL_loadbuffer: stp x29,x30,[sp,#-0x30]!; str x21,[sp,#0x10]; stp x20,x19,[sp,#0x20]; mov x29,sp
static const uint8_t SIG_LOADBUF[] = {
    0xFD,0x7B,0xBD,0xA9, 0xF5,0x0B,0x00,0xF9,
    0xF4,0x4F,0x02,0xA9, 0xFD,0x03,0x00,0x91,
};

// lua_pcall: stp x29,x30,[sp,#-0x20]!; stp x20,x19,[sp,#0x10]; mov x29,sp; mov x19,x0
static const uint8_t SIG_PCALL[] = {
    0xFD,0x7B,0xBE,0xA9, 0xF4,0x4F,0x01,0xA9,
    0xFD,0x03,0x00,0x91, 0xF3,0x03,0x00,0xAA,
};

// --- Logging ---
static void logmsg(NSString *fmt, ...) {
    va_list ap; char b[1024];
    va_start(ap, fmt); vsnprintf(b, sizeof b, [fmt UTF8String], ap); va_end(ap);
    NSLog(@"[RbxHook] %s", b);
}

// --- Hooks ---
static int my_loadbuffer(void *L, const char *buf, size_t sz, const char *name) {
    if (!g_L && L) { g_L = L; logmsg(@"captured L=%p (loadbuffer)", L); }
    return g_lb_orig(L, buf, sz, name);
}

static int my_pcall(void *L, int nargs, int nres, int errfunc) {
    if (!g_L && L) { g_L = L; logmsg(@"captured L=%p (pcall)", L); }
    return g_pc_orig(L, nargs, nres, errfunc);
}

// --- Sig Scan Helpers ---
static void *find_symbol_in_image(const struct mach_header_64 *hdr, const char *target) {
    const struct segment_command_64 *linkedit = NULL;
    const struct symtab_command *symtab = NULL;
    uintptr_t base = (uintptr_t)hdr;
    const uint8_t *p = (const uint8_t *)hdr + sizeof(struct mach_header_64);

    for (uint32_t i = 0; i < hdr->ncmds; i++) {
        const struct load_command *lc = (const struct load_command *)p;
        if (lc->cmd == LC_SEGMENT_64) {
            const struct segment_command_64 *seg = (const struct segment_command_64 *)lc;
            if (strncmp(seg->segname, "__LINKEDIT", 10) == 0) linkedit = seg;
        } else if (lc->cmd == LC_SYMTAB) {
            symtab = (const struct symtab_command *)lc;
        }
        p += lc->cmdsize;
    }
    if (!symtab || !linkedit) return NULL;

    uintptr_t le_start = base + linkedit->vmaddr;
    uintptr_t le_size = linkedit->filesize;

    if (symtab->stroff >= le_size || symtab->stroff + symtab->strsize > le_size ||
        symtab->symoff >= le_size || symtab->symoff + symtab->nsyms * sizeof(struct nlist_64) > le_size)
        return NULL;

    const char *strtab = (const char *)(le_start + symtab->stroff);
    const struct nlist_64 *syms = (const struct nlist_64 *)(le_start + symtab->symoff);

    for (uint32_t i = 0; i < symtab->nsyms; i++) {
        if (syms[i].n_un.n_strx == 0 || syms[i].n_un.n_strx >= symtab->strsize) continue;
        if (syms[i].n_value == 0) continue;
        const char *name = strtab + syms[i].n_un.n_strx;
        if (name[0] == '_') name++;
        if (strcmp(name, target) == 0) return (void *)(base + syms[i].n_value);
    }
    return NULL;
}

static void *find_any_symbol(const char *name) {
    uint32_t count = _dyld_image_count();
    for (uint32_t i = 0; i < count; i++) {
        const struct mach_header_64 *hdr = (const struct mach_header_64 *)_dyld_get_image_header(i);
        if (!hdr || hdr->magic != MH_MAGIC_64) continue;
        void *found = find_symbol_in_image(hdr, name);
        if (found) return found;
    }
    return NULL;
}

static void *scan_text_for_sig(const uint8_t *sig, size_t sig_len, const char **out_image) {
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

static void install_hooks(void) {
    void *pcall = find_any_symbol("lua_pcall");
    void *lb = find_any_symbol("luaL_loadbuffer");

    if (!pcall) {
        const char *img = NULL;
        pcall = scan_text_for_sig(SIG_PCALL, sizeof SIG_PCALL, &img);
        if (pcall) logmsg(@"lua_pcall prologue match @ %p in %s", pcall, img ? img : "?");
    }
    if (!lb) {
        const char *img = NULL;
        lb = scan_text_for_sig(SIG_LOADBUF, sizeof SIG_LOADBUF, &img);
        if (lb) logmsg(@"luaL_loadbuffer prologue match @ %p in %s", lb, img ? img : "?");
    }

    if (lb) DobbyHook(lb, (void *)my_loadbuffer, (void **)&g_lb_orig);
    if (pcall) DobbyHook(pcall, (void *)my_pcall, (void **)&g_pc_orig);
    
    logmsg(@"Hooks installed (pcall=%p, lb=%p)", pcall, lb);
}

// --- Server ---
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
    int opt = 1;
    setsockopt(g_srv, SOL_SOCKET, SO_REUSEADDR, &opt, sizeof opt);
    struct sockaddr_in a = {0};
    a.sin_family = AF_INET;
    a.sin_addr.s_addr = htonl(INADDR_LOOPBACK);
    a.sin_port = htons(HOOK_PORT);
    bind(g_srv, (struct sockaddr *)&a, sizeof a);
    listen(g_srv, 4);
    logmsg(@"listening on 127.0.0.1:%d", HOOK_PORT);

    for (;;) {
        int cli = accept(g_srv, NULL, NULL);
        if (cli < 0) continue;
        struct timeval tv = { 15, 0 };
        setsockopt(cli, SOL_SOCKET, SO_RCVTIMEO, &tv, sizeof tv);
        char hdr[256], nhdr[256];
        if (read_line(cli, hdr, sizeof hdr) < 0) { close(cli); continue; }
        long n = -1;
        sscanf(hdr, "SIZE %ld", &n);
        if (read_line(cli, nhdr, sizeof nhdr) < 0) { close(cli); continue; }
        
        size_t got = 0;
        while (got < (size_t)n) {
            ssize_t r = read(cli, g_script + got, n - got);
            if (r <= 0) break;
            got += r;
        }
        g_script[got] = 0;
        
        int rc = -1;
        if (g_L && g_lb_orig && g_pc_orig) {
            rc = g_lb_orig(g_L, g_script, got, "=rbxexec");
            if (rc == 0) rc = g_pc_orig(g_L, 0, 0, 0);
        }
        
        write(cli, rc == 0 ? "0 OK\n" : "1 ERR\n", 7);
        close(cli);
    }
    return NULL;
}

__attribute__((constructor))
static void on_load(void) {
    logmsg(@"libRbxHook loaded");
    install_hooks();
    pthread_t t;
    pthread_create(&t, NULL, server_thread, NULL);
    pthread_detach(t);
}
