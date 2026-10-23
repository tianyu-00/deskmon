/*
 * deskmon.c - Conky-style desktop system monitor for Windows (native Win32).
 *
 * Build (MinGW-w64):
 *   gcc -Os -s -mwindows deskmon.c -o deskmon.exe -luser32 -lgdi32 -ladvapi32 -liphlpapi -lws2_32 -lshell32
 * Build (MSVC, "x64 Native Tools" prompt):
 *   cl /O1 deskmon.c /link /SUBSYSTEM:WINDOWS
 *
 * Tray icon: right-click for the menu, double-click to show/hide the panel.
 * Quit: tray menu > Exit, or Ctrl+Alt+Q.
 * Settings are saved in HKEY_CURRENT_USER\Software\deskmon.
 */

#define WIN32_LEAN_AND_MEAN
#ifndef _WIN32_WINNT
#define _WIN32_WINNT 0x0A00
#endif
#include <winsock2.h>
#include <ws2tcpip.h>
#include <windows.h>
#include <shellapi.h>
#include <iphlpapi.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <wchar.h>

#ifdef _MSC_VER
#pragma comment(lib, "user32.lib")
#pragma comment(lib, "gdi32.lib")
#pragma comment(lib, "advapi32.lib")
#pragma comment(lib, "iphlpapi.lib")
#pragma comment(lib, "ws2_32.lib")
#pragma comment(lib, "shell32.lib")
#endif

/* ------------------------------------------------------------------ settings */
#define SCALE             1.4     /* overall size: 1.0 = original, 1.4 = 40% bigger */
#define BASE_WIDTH        300     /* panel width at SCALE 1.0, 96 DPI */
#define MARGIN_X          24      /* gap from the right edge of the screen */
#define MARGIN_Y          24      /* gap from the top of the screen */
#define TOP_N             4       /* processes shown per list */
#define SLOW_EVERY        10      /* disk usage + IP refresh every N seconds */
#define FONT_FACE         L"Consolas"
#define FONT_PT           10.0
#define TEXT_COL          RGB(255, 255, 255)
#define DIM_COL           RGB(200, 200, 200)
#define BAR_COL           RGB(216, 216, 216)
#define SHADOW            1       /* drop shadow so text is readable on light wallpapers */
#define SHADOW_COL        RGB(0, 0, 0)
#define CLICK_THROUGH     1       /* mouse clicks pass through to the desktop */
#define PAUSE_WHEN_HIDDEN 1       /* stop collecting/drawing during fullscreen apps or when locked */
#define KEY_COL           RGB(1, 1, 1) /* becomes fully transparent - don't use it elsewhere */
#define ICON_COL          0xFF3FC1C9u  /* tray icon bars (ARGB) - teal reads on light and dark taskbars */
/* --------------------------------------------------------------------------- */

#define MAXP 4096
#define MAXDISK 26

/* sections the user can switch on/off from the tray menu */
enum {
    SEC_SYSTEM = 1, SEC_PCPU = 2, SEC_PMEM = 4, SEC_RES = 8, SEC_DISK = 16, SEC_NET = 32,
    SEC_ALL = 63
};
static const struct { DWORD bit; const WCHAR *name; } SECTIONS[] = {
    { SEC_SYSTEM, L"System" },
    { SEC_PCPU,   L"Top processes (CPU)" },
    { SEC_PMEM,   L"Top processes (memory)" },
    { SEC_RES,    L"CPU / RAM / swap" },
    { SEC_DISK,   L"Disks" },
    { SEC_NET,    L"Network" },
};
#define NSECTIONS ((int)(sizeof SECTIONS / sizeof SECTIONS[0]))

#define WM_TRAY      (WM_APP + 1)
#define ID_SHOW      100
#define ID_STARTUP   101
#define ID_EXIT      102
#define ID_SEC_BASE  200
#define REG_KEY      L"Software\\deskmon"
#define RUN_KEY      L"Software\\Microsoft\\Windows\\CurrentVersion\\Run"
#define RUN_VALUE    L"deskmon"

/* ---- native structures (64-bit layout) */
typedef struct {
    ULONG NextEntryOffset;          /* 0   */
    ULONG NumberOfThreads;          /* 4   */
    LARGE_INTEGER Reserved[3];      /* 8   */
    LARGE_INTEGER CreateTime;       /* 32  */
    LARGE_INTEGER UserTime;         /* 40  */
    LARGE_INTEGER KernelTime;       /* 48  */
    USHORT NameLength;              /* 56  */
    USHORT NameMaxLength;           /* 58  */
    PWSTR NameBuffer;               /* 64  */
    LONG BasePriority;              /* 72  */
    HANDLE UniqueProcessId;         /* 80  */
    HANDLE InheritedFromProcessId;  /* 88  */
    ULONG HandleCount;              /* 96  */
    ULONG SessionId;                /* 100 */
    ULONG_PTR UniqueProcessKey;     /* 104 */
    SIZE_T PeakVirtualSize;         /* 112 */
    SIZE_T VirtualSize;             /* 120 */
    ULONG PageFaultCount;           /* 128 */
    SIZE_T PeakWorkingSetSize;      /* 136 */
    SIZE_T WorkingSetSize;          /* 144 */
} SPI;

#ifdef _WIN64
typedef char spi_layout_check[(offsetof(SPI, UniqueProcessId) == 80 &&
                               offsetof(SPI, WorkingSetSize) == 144) ? 1 : -1];
#endif

typedef struct {
    ULONG NextEntryOffset;
    ULONG TotalSize;    /* pages */
    ULONG TotalInUse;   /* pages */
    ULONG PeakUsage;
    USHORT NameLength, NameMaxLength;
    PWSTR NameBuffer;
} SPFI;

typedef LONG (NTAPI *NtQSI_t)(ULONG, PVOID, ULONG, PULONG);
typedef LONG (NTAPI *RtlGetVersion_t)(PRTL_OSVERSIONINFOW);
static NtQSI_t NtQSI;

/* ---- state */
typedef struct {
    ULONG_PTR pid;
    LONGLONG create, cpu;
    SIZE_T ws;
    double pct;
    WCHAR name[40];
} Proc;

static Proc pa[MAXP], pb[MAXP];
static Proc *cur = pa, *prv = pb;
static int ncur, nprv;
static BYTE *pbuf;
static ULONG pbufsz;
static int top_cpu[TOP_N], top_mem[TOP_N], ntop;

static WCHAR host[64], user[64], osname[64], ip[48] = L"";
static int ncpu = 1;
static DWORD page = 4096;
static double cpu_pct, ram_pct, ram_used, ram_total, swap_used, swap_total;
static double net_up, net_down, net_tot_up, net_tot_down;
static ULONGLONG prev_idle, prev_sys;
static ULONG64 prev_in, prev_out;
static int net_fresh;               /* 0 = next network sample only sets the baseline */
static LARGE_INTEGER qpf, prev_qpc, prev_proc_qpc;
static WCHAR disk_root[MAXDISK][4];
static double disk_used[MAXDISK], disk_total[MAXDISK];
static int disk_ok[MAXDISK], ndisk, slow_count = SLOW_EVERY;

static DWORD sections = SEC_ALL;    /* saved */
static int panel_visible = 1;       /* saved */

/* ---- drawing */
static double S;
static int W, H, LH, SH, GAP, INSET;
static HFONT font, font_bold;
static HPEN pen_dim, pen_shadow;
static HBRUSH br_bar, br_key;
static HDC g_dc;
static int Y;
static HDC memdc;
static HBITMAP membmp;
static int mem_w, mem_h;
static HWND g_hwnd;                 /* the panel */

/* ---- tray */
static HWND g_tray;                 /* hidden window that owns the icon and menu */
static NOTIFYICONDATAW nid;
static HICON tray_icon;
static UINT WM_TASKBARCREATED;
static int tray_ok;
static WCHAR last_tip[128];

/* ================================================================== helpers */
static void fmt_bytes(double n, WCHAR *o)
{
    static const WCHAR units[] = L"BKMGT";
    int i = 0;
    while (n >= 1024 && i < 4) { n /= 1024; i++; }
    if (i < 3) _snwprintf(o, 24, L"%.0f%c", n, units[i]);
    else       _snwprintf(o, 24, L"%.2f%c", n, units[i]);
}

static void fmt_uptime(ULONGLONG secs, WCHAR *o)
{
    unsigned d = (unsigned)(secs / 86400), h = (unsigned)(secs / 3600 % 24),
             m = (unsigned)(secs / 60 % 60), s = (unsigned)(secs % 60);
    if (d) _snwprintf(o, 32, L"%ud %uh %um", d, h, m);
    else   _snwprintf(o, 32, L"%uh %um %us", h, m, s);
}

static void trunc_name(const WCHAR *s, int n, WCHAR *o)
{
    int len = (int)wcslen(s);
    if (len <= n) { wcscpy(o, s); return; }
    wmemcpy(o, s, n - 1);
    o[n - 1] = 0x2026; /* … */
    o[n] = 0;
}

static ULONGLONG ft64(FILETIME f) { return ((ULONGLONG)f.dwHighDateTime << 32) | f.dwLowDateTime; }

static double qpc_since(LARGE_INTEGER *prev, LARGE_INTEGER now)
{
    double dt = (double)(now.QuadPart - prev->QuadPart) / (double)qpf.QuadPart;
    *prev = now;
    return dt > 1e-3 ? dt : 1e-3;
}

/* ================================================================== saved settings */
static void load_settings(void)
{
    HKEY k;
    if (RegOpenKeyExW(HKEY_CURRENT_USER, REG_KEY, 0, KEY_READ, &k) != ERROR_SUCCESS) return;
    DWORD v, sz = sizeof v, t;
    if (RegQueryValueExW(k, L"Sections", NULL, &t, (BYTE *)&v, &sz) == ERROR_SUCCESS && t == REG_DWORD)
        sections = v & SEC_ALL;
    sz = sizeof v;
    if (RegQueryValueExW(k, L"Visible", NULL, &t, (BYTE *)&v, &sz) == ERROR_SUCCESS && t == REG_DWORD)
        panel_visible = v != 0;
    RegCloseKey(k);
}

static void save_settings(void)
{
    HKEY k;
    if (RegCreateKeyExW(HKEY_CURRENT_USER, REG_KEY, 0, NULL, 0, KEY_WRITE, NULL, &k, NULL) != ERROR_SUCCESS)
        return;
    DWORD v = sections;
    RegSetValueExW(k, L"Sections", 0, REG_DWORD, (const BYTE *)&v, sizeof v);
    v = (DWORD)panel_visible;
    RegSetValueExW(k, L"Visible", 0, REG_DWORD, (const BYTE *)&v, sizeof v);
    RegCloseKey(k);
}

static void exe_command(WCHAR *out, int n)
{
    WCHAR path[MAX_PATH];
    GetModuleFileNameW(NULL, path, MAX_PATH);
    _snwprintf(out, n, L"\"%ls\"", path);
    out[n - 1] = 0;
}

/* "Start with Windows" = a value under HKCU\...\Run pointing at this exe */
static int startup_enabled(void)
{
    WCHAR want[MAX_PATH + 3], have[MAX_PATH + 3];
    HKEY k;
    int on = 0;
    memset(have, 0, sizeof have);
    exe_command(want, MAX_PATH + 3);
    if (RegOpenKeyExW(HKEY_CURRENT_USER, RUN_KEY, 0, KEY_READ, &k) == ERROR_SUCCESS) {
        DWORD sz = sizeof have - sizeof(WCHAR), t;
        if (RegQueryValueExW(k, RUN_VALUE, NULL, &t, (BYTE *)have, &sz) == ERROR_SUCCESS && t == REG_SZ)
            on = _wcsicmp(have, want) == 0; /* an old path (exe moved) counts as off */
        RegCloseKey(k);
    }
    return on;
}

static void set_startup(int on)
{
    HKEY k;
    if (RegOpenKeyExW(HKEY_CURRENT_USER, RUN_KEY, 0, KEY_SET_VALUE, &k) != ERROR_SUCCESS) return;
    if (on) {
        WCHAR cmd[MAX_PATH + 3];
        exe_command(cmd, MAX_PATH + 3);
        RegSetValueExW(k, RUN_VALUE, 0, REG_SZ, (const BYTE *)cmd,
                       (DWORD)((wcslen(cmd) + 1) * sizeof(WCHAR)));
    } else {
        RegDeleteValueW(k, RUN_VALUE);
    }
    RegCloseKey(k);
}

/* ================================================================== data */
static int cmp_pid(const void *a, const void *b)
{
    ULONG_PTR x = ((const Proc *)a)->pid, y = ((const Proc *)b)->pid;
    return x < y ? -1 : x > y;
}

/* Every process's name, CPU time and working set from ONE system call. */
static void sample_procs(void)
{
    ULONG ret = 0;
    LONG st;
    for (;;) {
        st = NtQSI(5 /* SystemProcessInformation */, pbuf, pbufsz, &ret);
        if ((ULONG)st == 0xC0000004UL) { /* STATUS_INFO_LENGTH_MISMATCH */
            ULONG want = ret + 65536 > pbufsz * 2 ? ret + 65536 : pbufsz * 2;
            free(pbuf);
            pbuf = (BYTE *)malloc(want);
            pbufsz = pbuf ? want : 0;
            if (!pbuf) return;
            continue;
        }
        break;
    }
    if (st != 0) return;

    LARGE_INTEGER now;
    QueryPerformanceCounter(&now);
    double span = qpc_since(&prev_proc_qpc, now) * 1e7 * ncpu; /* 100ns units, all cores */

    Proc *t = prv; prv = cur; nprv = ncur; cur = t; ncur = 0;

    BYTE *p = pbuf;
    for (;;) {
        SPI *e = (SPI *)p;
        if (e->UniqueProcessId && ncur < MAXP) {
            Proc *c = &cur[ncur++], key;
            c->pid = (ULONG_PTR)e->UniqueProcessId;
            c->create = e->CreateTime.QuadPart;
            c->cpu = e->UserTime.QuadPart + e->KernelTime.QuadPart;
            c->ws = e->WorkingSetSize;
            key.pid = c->pid;
            Proc *o = (Proc *)bsearch(&key, prv, nprv, sizeof(Proc), cmp_pid);
            if (o && o->create == c->create) {
                c->pct = (double)(c->cpu - o->cpu) / span * 100.0;
                if (c->pct < 0) c->pct = 0;
                memcpy(c->name, o->name, sizeof c->name);
            } else { /* new process: copy its name once */
                int n = e->NameLength / 2;
                if (n > 39) n = 39;
                if (e->NameBuffer && n) wmemcpy(c->name, e->NameBuffer, n);
                else { wcscpy(c->name, L"?"); n = 1; }
                c->name[n] = 0;
                c->pct = 0;
            }
        }
        if (!e->NextEntryOffset) break;
        p += e->NextEntryOffset;
    }
    qsort(cur, ncur, sizeof(Proc), cmp_pid);

    /* pick top N by CPU and by memory */
    ntop = ncur < TOP_N ? ncur : TOP_N;
    for (int k = 0; k < ntop; k++) {
        int bc = -1, bm = -1;
        for (int i = 0; i < ncur; i++) {
            int used_c = 0, used_m = 0;
            for (int j = 0; j < k; j++) {
                if (top_cpu[j] == i) used_c = 1;
                if (top_mem[j] == i) used_m = 1;
            }
            if (!used_c && (bc < 0 || cur[i].pct > cur[bc].pct)) bc = i;
            if (!used_m && (bm < 0 || cur[i].ws > cur[bm].ws)) bm = i;
        }
        top_cpu[k] = bc;
        top_mem[k] = bm;
    }
}

static void sample_swap(void)
{
    BYTE buf[4096];
    ULONG ret = 0;
    swap_used = swap_total = 0;
    if (NtQSI(18 /* SystemPageFileInformation */, buf, sizeof buf, &ret) != 0 || ret == 0) return;
    BYTE *p = buf;
    for (;;) {
        SPFI *e = (SPFI *)p;
        swap_total += (double)e->TotalSize * page;
        swap_used += (double)e->TotalInUse * page;
        if (!e->NextEntryOffset) break;
        p += e->NextEntryOffset;
    }
}

static void net_totals(ULONG64 *in, ULONG64 *out)
{
    PMIB_IF_TABLE2 t;
    *in = *out = 0;
    if (GetIfTable2(&t) != NO_ERROR) return;
    for (ULONG i = 0; i < t->NumEntries; i++) {
        MIB_IF_ROW2 *r = &t->Table[i];
        /* physical adapters only, so filter/virtual layers aren't double counted */
        if (!r->InterfaceAndOperStatusFlags.HardwareInterface ||
            r->InterfaceAndOperStatusFlags.FilterInterface) continue;
        *in += r->InOctets;
        *out += r->OutOctets;
    }
    FreeMibTable(t);
}

static void get_ip(void)
{
    /* UDP "connect" sends nothing; it just picks the outbound interface */
    wcscpy(ip, L"offline");
    SOCKET s = socket(AF_INET, SOCK_DGRAM, IPPROTO_UDP);
    if (s == INVALID_SOCKET) return;
    struct sockaddr_in a;
    memset(&a, 0, sizeof a);
    a.sin_family = AF_INET;
    a.sin_port = htons(80);
    a.sin_addr.s_addr = htonl(0x08080808);
    if (connect(s, (struct sockaddr *)&a, sizeof a) == 0) {
        struct sockaddr_in l;
        int n = sizeof l;
        if (getsockname(s, (struct sockaddr *)&l, &n) == 0)
            InetNtopW(AF_INET, &l.sin_addr, ip, 48);
    }
    closesocket(s);
}

static void sample_disks(void)
{
    for (int i = 0; i < ndisk; i++) {
        ULARGE_INTEGER total, freeb;
        disk_ok[i] = GetDiskFreeSpaceExW(disk_root[i], NULL, &total, &freeb) != 0;
        if (disk_ok[i]) {
            disk_total[i] = (double)total.QuadPart;
            disk_used[i] = (double)(total.QuadPart - freeb.QuadPart);
        }
    }
}

/* CPU and RAM are two cheap calls; they also feed the tray tooltip */
static void sample_cpu_ram(void)
{
    FILETIME idle, kern, usr;
    if (GetSystemTimes(&idle, &kern, &usr)) {
        ULONGLONG i = ft64(idle), s = ft64(kern) + ft64(usr); /* kernel time includes idle */
        ULONGLONG ds = s - prev_sys, di = i - prev_idle;
        cpu_pct = ds ? 100.0 * (double)(ds - di) / (double)ds : 0;
        prev_sys = s; prev_idle = i;
    }
    MEMORYSTATUSEX ms;
    ms.dwLength = sizeof ms;
    if (GlobalMemoryStatusEx(&ms)) {
        ram_total = (double)ms.ullTotalPhys;
        ram_used = (double)(ms.ullTotalPhys - ms.ullAvailPhys);
        ram_pct = ms.dwMemoryLoad;
    }
}

/* Collects only what the visible sections need. */
static void collect(void)
{
    sample_cpu_ram();
    if (sections & (SEC_PCPU | SEC_PMEM)) sample_procs();
    if (sections & SEC_RES) sample_swap();

    if (++slow_count >= SLOW_EVERY) {
        slow_count = 0;
        if (sections & SEC_DISK) sample_disks();
        if (sections & SEC_NET) get_ip();
    }

    if (sections & SEC_NET) {
        ULONG64 in, out;
        LARGE_INTEGER now;
        net_totals(&in, &out);
        QueryPerformanceCounter(&now);
        double dt = qpc_since(&prev_qpc, now);
        if (net_fresh && in >= prev_in && out >= prev_out) {
            net_down = (double)(in - prev_in) / dt;
            net_up = (double)(out - prev_out) / dt;
        } else {
            net_down = net_up = 0; /* first sample after (re)enabling: baseline only */
        }
        net_fresh = 1;
        prev_in = in; prev_out = out;
        net_tot_down = (double)in;
        net_tot_up = (double)out;
    } else {
        net_fresh = 0;
    }
}

/* ================================================================== rendering */
static void text_at(int x, const WCHAR *s, COLORREF c, UINT align)
{
    int n = (int)wcslen(s);
    if (!n) return;
    SetTextAlign(g_dc, align | TA_TOP | TA_NOUPDATECP);
    if (SHADOW) {
        SetTextColor(g_dc, SHADOW_COL);
        TextOutW(g_dc, x + SH, Y + SH, s, n);
    }
    SetTextColor(g_dc, c);
    TextOutW(g_dc, x, Y, s, n);
}

static void hline(HPEN pen, int x0, int x1, int y)
{
    SelectObject(g_dc, pen);
    MoveToEx(g_dc, x0, y, NULL);
    LineTo(g_dc, x1, y);
}

static void header(const WCHAR *t)
{
    SIZE sz;
    Y += GAP;
    SelectObject(g_dc, font_bold);
    text_at(0, t, TEXT_COL, TA_LEFT);
    GetTextExtentPoint32W(g_dc, t, (int)wcslen(t), &sz);
    SelectObject(g_dc, font);
    int mid = Y + LH / 2, x0 = sz.cx + (int)(8 * S);
    if (SHADOW) hline(pen_shadow, x0 + SH, W - 2 + SH, mid + SH);
    hline(pen_dim, x0, W - 2, mid);
    Y += LH;
}

static void row(const WCHAR *l, const WCHAR *r, COLORREF c)
{
    text_at(0, l, c, TA_LEFT);
    text_at(W - 2, r, c, TA_RIGHT);
    Y += LH;
}

static void bar_row(const WCHAR *label, double pct)
{
    text_at(0, label, TEXT_COL, TA_LEFT);
    int x0 = (int)(W * 0.55), x1 = W - 2, y0 = Y + INSET, y1 = Y + LH - INSET;
    SelectObject(g_dc, GetStockObject(NULL_BRUSH));
    if (SHADOW) {
        SelectObject(g_dc, pen_shadow);
        Rectangle(g_dc, x0 + SH, y0 + SH, x1 + SH, y1 + SH);
    }
    SelectObject(g_dc, pen_dim);
    Rectangle(g_dc, x0, y0, x1, y1);
    if (pct < 0) pct = 0;
    if (pct > 100) pct = 100;
    int fx = x0 + SH + (int)((x1 - x0 - 2 * SH) * pct / 100.0);
    if (fx > x0 + SH) {
        RECT r = { x0 + SH, y0 + SH, fx, y1 - SH };
        FillRect(g_dc, &r, br_bar);
    }
    Y += LH;
}

/* Draws the enabled sections; returns the panel height. */
static int render(HDC dc)
{
    WCHAR a[64], b[64], c[64];
    g_dc = dc;
    Y = 0;
    SetBkMode(dc, TRANSPARENT);
    SelectObject(dc, font);

    if (sections & SEC_SYSTEM) {
        header(L"SYSTEM");
        row(host, L"", TEXT_COL);
        row(user, L"", TEXT_COL);
        row(osname, L"", TEXT_COL);
        fmt_uptime(GetTickCount64() / 1000, b);
        row(L"Uptime", b, TEXT_COL);
    }

    if (sections & (SEC_PCPU | SEC_PMEM)) {
        header(L"PROCESSES");
        if (sections & SEC_PCPU) {
            row(L"", L"CPU% used", DIM_COL);
            for (int i = 0; i < TOP_N; i++) {
                if (i < ntop) {
                    Proc *p = &cur[top_cpu[i]];
                    trunc_name(p->name, 22, a);
                    _snwprintf(b, 64, L"%.2f %%", p->pct);
                    row(a, b, TEXT_COL);
                } else row(L"", L"", TEXT_COL);
            }
        }
        if (sections & SEC_PMEM) {
            row(L"", L"MEM used", DIM_COL);
            for (int i = 0; i < TOP_N; i++) {
                if (i < ntop) {
                    Proc *p = &cur[top_mem[i]];
                    trunc_name(p->name, 22, a);
                    fmt_bytes((double)p->ws, b);
                    row(a, b, TEXT_COL);
                } else row(L"", L"", TEXT_COL);
            }
        }
    }

    if (sections & SEC_RES) {
        header(L"RESOURCES");
        _snwprintf(a, 64, L"CPU: %.0f%%", cpu_pct);
        bar_row(a, cpu_pct);
        _snwprintf(a, 64, L"RAM: %.0f%%", ram_pct);
        bar_row(a, ram_pct);
        fmt_bytes(ram_used, b); fmt_bytes(ram_total, c);
        _snwprintf(a, 64, L"%ls / %ls", b, c);
        row(L"", a, TEXT_COL);
        double sp = swap_total > 0 ? swap_used / swap_total * 100.0 : 0;
        _snwprintf(a, 64, L"Swap: %.0f%%", sp);
        bar_row(a, sp);
        fmt_bytes(swap_used, b); fmt_bytes(swap_total, c);
        _snwprintf(a, 64, L"%ls / %ls", b, c);
        row(L"", a, TEXT_COL);
    }

    if ((sections & SEC_DISK) && ndisk) {
        header(L"DISKS");
        for (int i = 0; i < ndisk; i++) {
            WCHAR label[3] = { disk_root[i][0], L':', 0 };
            if (disk_ok[i] && disk_total[i] > 0) {
                double dp = disk_used[i] / disk_total[i] * 100.0;
                _snwprintf(a, 64, L"%ls %.0f%%", label, dp);
                bar_row(a, dp);
                fmt_bytes(disk_used[i], b); fmt_bytes(disk_total[i], c);
                _snwprintf(a, 64, L"%ls / %ls", b, c);
                row(L"", a, TEXT_COL);
            } else {
                _snwprintf(a, 64, L"%ls n/a", label);
                bar_row(a, 0);
                row(L"", L"", TEXT_COL);
            }
        }
    }

    if (sections & SEC_NET) {
        header(L"NETWORK");
        row(L"IP", ip, TEXT_COL);
        fmt_bytes(net_up, b);   wcscat(b, L"/s"); row(L"Up", b, TEXT_COL);
        fmt_bytes(net_down, b); wcscat(b, L"/s"); row(L"Down", b, TEXT_COL);
        fmt_bytes(net_tot_up, b);   row(L"Total Up", b, TEXT_COL);
        fmt_bytes(net_tot_down, b); row(L"Total Down", b, TEXT_COL);
    }

    return Y + 4;
}

/* ================================================================== visibility */
static int is_locked(void)
{
    /* the input desktop can't be opened while the lock screen is up */
    HDESK h = OpenInputDesktop(0, FALSE, DESKTOP_SWITCHDESKTOP);
    if (!h) return 1;
    CloseDesktop(h);
    return 0;
}

static int fullscreen_over(HWND own)
{
    HWND fg = GetForegroundWindow();
    WCHAR cls[64];
    if (!fg || fg == own) return 0;
    GetClassNameW(fg, cls, 64);
    if (!wcscmp(cls, L"Progman") || !wcscmp(cls, L"WorkerW") || !wcscmp(cls, L"Shell_TrayWnd"))
        return 0; /* the desktop itself */
    HMONITOR mon = MonitorFromWindow(fg, MONITOR_DEFAULTTONEAREST);
    if (mon != MonitorFromWindow(own, MONITOR_DEFAULTTONEAREST)) return 0;
    MONITORINFO mi;
    mi.cbSize = sizeof mi;
    RECT r;
    if (!GetMonitorInfoW(mon, &mi) || !GetWindowRect(fg, &r)) return 0;
    return r.left <= mi.rcMonitor.left && r.top <= mi.rcMonitor.top &&
           r.right >= mi.rcMonitor.right && r.bottom >= mi.rcMonitor.bottom;
}

/* ================================================================== panel window */
static UINT next_delay(void)
{
    /* land just after the next uptime-second boundary so seconds never skip */
    return (UINT)(1000 - GetTickCount64() % 1000 + 20);
}

static int measure_height(void)
{
    HDC sdc = GetDC(NULL), mdc = CreateCompatibleDC(sdc);
    int h = render(mdc);
    DeleteDC(mdc);
    ReleaseDC(NULL, sdc);
    return h;
}

static void place_window(void)
{
    int x = GetSystemMetrics(SM_CXSCREEN) - W - (int)(MARGIN_X * S / SCALE);
    int y = (int)(MARGIN_Y * S / SCALE);
    SetWindowPos(g_hwnd, HWND_BOTTOM, x, y, W, H, SWP_NOACTIVATE);
}

/* after the set of sections changes: fresh data, new height, redraw */
static void relayout(void)
{
    slow_count = SLOW_EVERY; /* newly shown disks/IP get read straight away */
    collect();
    H = measure_height();
    place_window();
    InvalidateRect(g_hwnd, NULL, FALSE);
}

static void tray_tip(void)
{
    WCHAR tip[128];
    _snwprintf(tip, 128, L"deskmon\nCPU %.0f%%   RAM %.0f%%", cpu_pct, ram_pct);
    tip[127] = 0;
    if (!tray_ok || !wcscmp(tip, last_tip)) return;
    wcscpy(last_tip, tip);
    wcscpy(nid.szTip, tip);
    nid.uFlags = NIF_TIP;
    Shell_NotifyIconW(NIM_MODIFY, &nid);
}

static void tray_add(void);

static void tick(HWND hwnd)
{
    if (!tray_ok) tray_add(); /* at login the taskbar may not be ready yet */

    int hidden = !panel_visible ||
                 (PAUSE_WHEN_HIDDEN && (is_locked() || fullscreen_over(hwnd)));
    if (hidden) {
        sample_cpu_ram(); /* tooltip only - skip everything else */
        net_fresh = 0;
        tray_tip();
        SetTimer(hwnd, 1, next_delay(), NULL);
        return;
    }
    collect();
    tray_tip();
    InvalidateRect(hwnd, NULL, FALSE);
    SetWindowPos(hwnd, HWND_BOTTOM, 0, 0, 0, 0, SWP_NOSIZE | SWP_NOMOVE | SWP_NOACTIVATE);
    SetTimer(hwnd, 1, next_delay(), NULL);
}

static void set_panel_visible(int on)
{
    panel_visible = on;
    save_settings();
    if (on) {
        relayout();
        ShowWindow(g_hwnd, SW_SHOWNOACTIVATE);
    } else {
        ShowWindow(g_hwnd, SW_HIDE);
    }
}

static LRESULT CALLBACK panelproc(HWND hwnd, UINT msg, WPARAM wp, LPARAM lp)
{
    switch (msg) {
    case WM_TIMER:
        KillTimer(hwnd, 1);
        tick(hwnd);
        return 0;
    case WM_ERASEBKGND:
        return 1;
    case WM_PAINT: {
        PAINTSTRUCT ps;
        HDC hdc = BeginPaint(hwnd, &ps);
        RECT rc;
        GetClientRect(hwnd, &rc);
        if (!memdc || mem_w != rc.right || mem_h != rc.bottom) {
            if (memdc) { DeleteDC(memdc); DeleteObject(membmp); }
            memdc = CreateCompatibleDC(hdc);
            membmp = CreateCompatibleBitmap(hdc, rc.right, rc.bottom);
            SelectObject(memdc, membmp);
            mem_w = rc.right; mem_h = rc.bottom;
        }
        FillRect(memdc, &rc, br_key);
        render(memdc);
        BitBlt(hdc, 0, 0, rc.right, rc.bottom, memdc, 0, 0, SRCCOPY);
        EndPaint(hwnd, &ps);
        return 0;
    }
    case WM_WINDOWPOSCHANGING: {
        WINDOWPOS *wpos = (WINDOWPOS *)lp;
        if (!(wpos->flags & SWP_NOZORDER)) wpos->hwndInsertAfter = HWND_BOTTOM;
        break; /* keep it under normal windows, like a desktop widget */
    }
    case WM_DISPLAYCHANGE:
        place_window();
        return 0;
    case WM_HOTKEY:
        DestroyWindow(hwnd);
        return 0;
    case WM_DESTROY:
        if (tray_ok) Shell_NotifyIconW(NIM_DELETE, &nid);
        PostQuitMessage(0);
        return 0;
    }
    return DefWindowProcW(hwnd, msg, wp, lp);
}

/* ================================================================== tray */
/* draws a small 3-bar chart icon, scaled to the system's small-icon size */
static HICON make_icon(void)
{
    int n = GetSystemMetrics(SM_CXSMICON);
    if (n < 16) n = 16;
    if (n > 64) n = 64;
    BITMAPINFO bi;
    memset(&bi, 0, sizeof bi);
    bi.bmiHeader.biSize = sizeof(BITMAPINFOHEADER);
    bi.bmiHeader.biWidth = n;
    bi.bmiHeader.biHeight = -n; /* top-down */
    bi.bmiHeader.biPlanes = 1;
    bi.bmiHeader.biBitCount = 32;
    bi.bmiHeader.biCompression = BI_RGB;
    DWORD *px = NULL;
    HDC dc = GetDC(NULL);
    HBITMAP color = CreateDIBSection(dc, &bi, DIB_RGB_COLORS, (void **)&px, NULL, 0);
    ReleaseDC(NULL, dc);
    if (!color || !px) return LoadIcon(NULL, IDI_APPLICATION);
    memset(px, 0, (size_t)n * n * 4);

    static const double heights[3] = { 0.50, 0.90, 0.68 };
    double u = n / 16.0;
    for (int b = 0; b < 3; b++) {
        int x0 = (int)((1 + 5 * b) * u + 0.5), x1 = (int)((5 + 5 * b) * u + 0.5);
        int y1 = n - (int)(1 * u + 0.5), y0 = y1 - (int)(heights[b] * 14 * u + 0.5);
        for (int y = y0; y < y1; y++)
            for (int x = x0; x < x1; x++)
                if (x >= 0 && x < n && y >= 0 && y < n) px[y * n + x] = ICON_COL;
    }

    int stride = ((n + 15) / 16) * 2;
    BYTE *zeros = (BYTE *)calloc((size_t)stride * n, 1);
    HBITMAP mask = CreateBitmap(n, n, 1, 1, zeros);
    free(zeros);
    ICONINFO ii;
    memset(&ii, 0, sizeof ii);
    ii.fIcon = TRUE;
    ii.hbmMask = mask;
    ii.hbmColor = color;
    HICON icon = CreateIconIndirect(&ii);
    DeleteObject(mask);
    DeleteObject(color);
    return icon ? icon : LoadIcon(NULL, IDI_APPLICATION);
}

static void tray_add(void)
{
    memset(&nid, 0, sizeof nid);
    nid.cbSize = sizeof nid;
    nid.hWnd = g_tray;
    nid.uID = 1;
    nid.uFlags = NIF_ICON | NIF_MESSAGE | NIF_TIP;
    nid.uCallbackMessage = WM_TRAY;
    nid.hIcon = tray_icon;
    wcscpy(nid.szTip, L"deskmon");
    last_tip[0] = 0;
    tray_ok = Shell_NotifyIconW(NIM_ADD, &nid) != 0;
}

static void show_menu(HWND hwnd)
{
    HMENU sub = CreatePopupMenu(), m = CreatePopupMenu();
    for (int i = 0; i < NSECTIONS; i++)
        AppendMenuW(sub, MF_STRING | ((sections & SECTIONS[i].bit) ? MF_CHECKED : 0),
                    ID_SEC_BASE + i, SECTIONS[i].name);
    AppendMenuW(m, MF_STRING | (panel_visible ? MF_CHECKED : 0), ID_SHOW, L"Show panel");
    AppendMenuW(m, MF_POPUP, (UINT_PTR)sub, L"Sections");
    AppendMenuW(m, MF_STRING | (startup_enabled() ? MF_CHECKED : 0), ID_STARTUP, L"Start with Windows");
    AppendMenuW(m, MF_SEPARATOR, 0, NULL);
    AppendMenuW(m, MF_STRING, ID_EXIT, L"Exit");

    POINT pt;
    GetCursorPos(&pt);
    SetForegroundWindow(hwnd); /* so the menu closes when you click elsewhere */
    TrackPopupMenu(m, TPM_RIGHTBUTTON, pt.x, pt.y, 0, hwnd, NULL);
    PostMessageW(hwnd, WM_NULL, 0, 0);
    DestroyMenu(m); /* also destroys the submenu */
}

static LRESULT CALLBACK trayproc(HWND hwnd, UINT msg, WPARAM wp, LPARAM lp)
{
    if (msg == WM_TRAY) {
        if (lp == WM_RBUTTONUP || lp == WM_CONTEXTMENU) show_menu(hwnd);
        else if (lp == WM_LBUTTONDBLCLK) set_panel_visible(!panel_visible);
        return 0;
    }
    if (WM_TASKBARCREATED && msg == WM_TASKBARCREATED) { /* Explorer restarted */
        tray_add();
        return 0;
    }
    if (msg == WM_COMMAND) {
        int id = LOWORD(wp);
        if (id == ID_SHOW) set_panel_visible(!panel_visible);
        else if (id == ID_STARTUP) set_startup(!startup_enabled());
        else if (id == ID_EXIT) DestroyWindow(g_hwnd);
        else if (id >= ID_SEC_BASE && id < ID_SEC_BASE + NSECTIONS) {
            sections ^= SECTIONS[id - ID_SEC_BASE].bit;
            save_settings();
            if (panel_visible) relayout();
        }
        return 0;
    }
    return DefWindowProcW(hwnd, msg, wp, lp);
}

/* ================================================================== startup */
static void init_static_info(void)
{
    DWORD n = 64;
    if (!GetComputerNameW(host, &n)) wcscpy(host, L"?");
    n = 64;
    if (!GetUserNameW(user, &n)) wcscpy(user, L"?");

    RTL_OSVERSIONINFOW v;
    memset(&v, 0, sizeof v);
    v.dwOSVersionInfoSize = sizeof v;
    RtlGetVersion_t rgv = (RtlGetVersion_t)(void *)GetProcAddress(GetModuleHandleW(L"ntdll.dll"), "RtlGetVersion");
    if (rgv && rgv(&v) == 0) {
        unsigned rel = v.dwMajorVersion == 10 && v.dwBuildNumber >= 22000 ? 11 : v.dwMajorVersion;
        _snwprintf(osname, 64, L"Windows %u (%u.%u.%u)", rel,
                   (unsigned)v.dwMajorVersion, (unsigned)v.dwMinorVersion, (unsigned)v.dwBuildNumber);
    } else wcscpy(osname, L"Windows");

    SYSTEM_INFO si;
    GetSystemInfo(&si);
    ncpu = si.dwNumberOfProcessors ? (int)si.dwNumberOfProcessors : 1;
    page = si.dwPageSize ? si.dwPageSize : 4096;

    DWORD mask = GetLogicalDrives();
    for (int i = 0; i < 26 && ndisk < MAXDISK; i++) {
        if (!(mask & (1u << i))) continue;
        WCHAR root[4] = { (WCHAR)(L'A' + i), L':', L'\\', 0 };
        if (GetDriveTypeW(root) == DRIVE_FIXED) wcscpy(disk_root[ndisk++], root);
    }
}

int WINAPI WinMain(HINSTANCE inst, HINSTANCE prev, LPSTR cmd, int show)
{
    (void)prev; (void)cmd; (void)show;

    /* one copy only (e.g. started from both Startup and by hand) */
    CreateMutexW(NULL, TRUE, L"deskmon-single-instance");
    if (GetLastError() == ERROR_ALREADY_EXISTS) return 0;

    SetProcessDPIAware();
    NtQSI = (NtQSI_t)(void *)GetProcAddress(GetModuleHandleW(L"ntdll.dll"), "NtQuerySystemInformation");
    if (!NtQSI) return 1;
    pbufsz = 1 << 20;
    pbuf = (BYTE *)malloc(pbufsz);
    QueryPerformanceFrequency(&qpf);
    QueryPerformanceCounter(&prev_qpc);
    prev_proc_qpc = prev_qpc;

    WSADATA wsa;
    WSAStartup(MAKEWORD(2, 2), &wsa);
    init_static_info();
    load_settings();

    /* sizes */
    HDC sdc = GetDC(NULL);
    int dpi = GetDeviceCaps(sdc, LOGPIXELSY);
    S = SCALE * dpi / 96.0;
    W = (int)(BASE_WIDTH * S);
    SH = (int)(S / 1.4 + 0.5); if (SH < 1) SH = 1;
    GAP = (int)(6 * S + 0.5);
    INSET = (int)(3 * S + 0.5);
    int fh = -(int)(FONT_PT * SCALE * dpi / 72.0 + 0.5);
    font = CreateFontW(fh, 0, 0, 0, FW_NORMAL, 0, 0, 0, DEFAULT_CHARSET, OUT_DEFAULT_PRECIS,
                       CLIP_DEFAULT_PRECIS, ANTIALIASED_QUALITY, FIXED_PITCH | FF_MODERN, FONT_FACE);
    font_bold = CreateFontW(fh, 0, 0, 0, FW_BOLD, 0, 0, 0, DEFAULT_CHARSET, OUT_DEFAULT_PRECIS,
                            CLIP_DEFAULT_PRECIS, ANTIALIASED_QUALITY, FIXED_PITCH | FF_MODERN, FONT_FACE);
    TEXTMETRICW tm;
    HGDIOBJ old = SelectObject(sdc, font);
    GetTextMetricsW(sdc, &tm);
    SelectObject(sdc, old);
    ReleaseDC(NULL, sdc);
    LH = tm.tmHeight + (int)(2 * S + 0.5);
    pen_dim = CreatePen(PS_SOLID, SH, DIM_COL);
    pen_shadow = CreatePen(PS_SOLID, SH, SHADOW_COL);
    br_bar = CreateSolidBrush(BAR_COL);
    br_key = CreateSolidBrush(KEY_COL);

    /* first sample primes the CPU counters; then measure the layout height */
    collect();
    H = measure_height();

    WNDCLASSW wc;
    memset(&wc, 0, sizeof wc);
    wc.lpfnWndProc = panelproc;
    wc.hInstance = inst;
    wc.hCursor = LoadCursor(NULL, IDC_ARROW);
    wc.lpszClassName = L"deskmon";
    RegisterClassW(&wc);
    wc.lpfnWndProc = trayproc;
    wc.lpszClassName = L"deskmon-tray";
    RegisterClassW(&wc);

    DWORD ex = WS_EX_LAYERED | WS_EX_TOOLWINDOW | WS_EX_NOACTIVATE;
    if (CLICK_THROUGH) ex |= WS_EX_TRANSPARENT;
    g_hwnd = CreateWindowExW(ex, L"deskmon", L"deskmon", WS_POPUP, 0, 0, W, H,
                             NULL, NULL, inst, NULL);
    /* hidden, never shown: owns the tray icon and its menu */
    g_tray = CreateWindowExW(WS_EX_TOOLWINDOW, L"deskmon-tray", L"deskmon tray", WS_POPUP,
                             0, 0, 0, 0, NULL, NULL, inst, NULL);
    if (!g_hwnd || !g_tray) return 1;

    SetLayeredWindowAttributes(g_hwnd, KEY_COL, 0, LWA_COLORKEY);
    RegisterHotKey(g_hwnd, 1, MOD_CONTROL | MOD_ALT | MOD_NOREPEAT, 'Q');

    WM_TASKBARCREATED = RegisterWindowMessageW(L"TaskbarCreated");
    tray_icon = make_icon();
    tray_add();

    place_window();
    if (panel_visible) ShowWindow(g_hwnd, SW_SHOWNOACTIVATE);
    SetTimer(g_hwnd, 1, next_delay(), NULL);

    MSG m;
    while (GetMessageW(&m, NULL, 0, 0) > 0) {
        TranslateMessage(&m);
        DispatchMessageW(&m);
    }
    WSACleanup();
    return 0;
}
