#!/usr/bin/env python3
# any front end is rendered by claude AI. all backend work is mine

import time, os, sys, socket, random, uuid, glob, csv

from threading    import Thread
from datetime     import datetime
from urllib.parse import urlparse
from PIL          import Image
from blessed      import Terminal

# ── escape helpers ────────────────────────────────────────────────────────────
RESET = "\033[0m"

def rgb(r, g, b):
    return f"\033[38;2;{r};{g};{b}m"

def rgb_bg(r, g, b):
    return f"\033[48;2;{r};{g};{b}m"

# ── tool imports ──────────────────────────────────────────────────────────────
try:
    from modes.web_scraper import web_scraper
except Exception:
    web_scraper = None

try:
    from modes.tls_inspect import tls_inspection
except Exception:
    tls_inspection = None


# ── batch helpers ─────────────────────────────────────────────────────────────

def load_tls_targets(path):
    """Read a host list. Accepts https://site.com/path, site.com, site.com:8443,
    blank lines and # comments. Returns a de-duplicated list of hostnames."""
    targets = []
    with open(path, encoding="utf-8", errors="ignore") as f:
        for line in f:
            line = line.split("#", 1)[0].strip()
            if not line:
                continue
            if "://" not in line:
                line = "https://" + line
            try:
                host = urlparse(line).hostname
            except ValueError:
                host = None
            if host:
                targets.append(host.lower())
    return list(dict.fromkeys(targets))


def expand_path(raw):
    return os.path.abspath(os.path.expanduser(raw.strip().strip('"').strip("'")))


# ─────────────────────────────────────────────────────────────────────────────
class Dashboard:

    THEMES = {
        "pipboy": {"name": "pipboy", "feed": "bright_green", "stats": "bright_green",  "matrix": (0, 255, 65)},
        "olive":  {"name": "olive",  "feed": "green",         "stats": "green",         "matrix": (0, 150, 40)},
        "bleed":  {"name": "bleed",  "feed": "bright_red",    "stats": "bright_red",    "matrix": (255, 30,  0)},
    }

    _RGB = {
        "bright_green":   (0,   255, 65),  "green":        (0,   150, 40),
        "bright_yellow":  (255, 255, 0),   "yellow":       (255, 176, 0),
        "bright_cyan":    (0,   255, 255), "cyan":         (0,   191, 255),
        "bright_magenta": (255, 0,   255), "magenta":      (255, 0,   255),
        "bright_blue":    (100, 149, 237), "blue":         (0,   0,   255),
        "bright_white":   (255, 255, 255), "white":        (200, 200, 200),
        "bright_red":     (255, 0,   0),   "red":          (200, 0,   0),
        "orange":         (255, 165, 0),   "purple":       (138, 43,  226),
    }

    _MATRIX_CHARS = (
        "ｦｧｨｩｪｫｬｭｮｯｰｱｲｳｴｵｶｷｸｹｺｻｼｽｾｿﾀﾁﾂﾃﾄﾅﾆﾇﾈﾉﾊﾋﾌﾍﾎﾏﾐﾑﾒﾓﾔﾕﾖﾗﾘﾙﾚﾛﾜﾝ"
        "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ@#$%&"
    )

    # ── scraper filter type → selector template mapping ─────────────────────
    FILTER_TEMPLATES = {
        "1": ("element", "{value}"),              # raw tag selector, e.g. h1, table, a, img
        "2": ("images",  "img[src*='{value}']"),  # image src contains value
        "3": ("keyword", ".{value}"),              # class selector
    }

    PLACEHOLDER_HINTS = {
        "element": "e.g. h1, div, table",
        "images":  "e.g. logo, banner, icon",
        "keyword": "e.g. price, product-title",
    }

    TLS_BATCH_TIMEOUT = 20   # seconds to wait per host if start() is non-blocking

    # ── init ──────────────────────────────────────────────────────────────────
    def __init__(self, theme="pipboy", animate=10):

        self.term                = Terminal()
        self.animate             = animate
        self.start_time          = time.time()
        self.theme_names         = list(self.THEMES)
        tidx                     = self.theme_names.index(theme) if theme in self.THEMES else 0
        self.current_theme_index = tidx
        self.theme               = self.THEMES[self.theme_names[tidx]]

        self.paused              = False
        self.show_legend         = False
        self.running             = True

        # tool references
        self.web_scraper_panel   = web_scraper
        self.tls_inspect_panel   = tls_inspection

        # panel visibility flags
        self.web_scraper_mode    = False
        self.tls_inspect_mode    = False

        # lifecycle  0=closed 1=input 2=running 3=done 4=batch
        self.web_scraper_state   = 0
        self.tls_inspect_state   = 0

        # input routing  None | "tls_host" | "tls_file" | "scraper_domain" | "scraper_filter_type" | "scraper_flag"
        self.active_input_mode   = None
        self.input_buffer        = ""
        self._scraper_domain     = ""

        # TLS batch state
        self.tls_batch_mode      = False
        self.tls_batch           = self._new_batch_state()
        self._last_batch_path    = ""
        self._path_matches       = []     # tab-completion candidates shown under prompt
        self._path_error         = ""

        # scraper filter selection state
        self._scraper_filter_key      = None
        self._scraper_filter_template = None
        self._scraper_filter_label    = None

        # scraper phase tracking
        # False = filter prompt not yet shown for this fetch
        # True  = filter prompt has been shown; do not show again
        self._scraper_filter_prompted = False
        # True only between _commit_input(scraper_flag) and search completion
        self._scraper_search_started  = False

        # matrix
        self.matrix_cols         = {}
        self.matrix_last_update  = 0.0

        # animations
        self.animations          = {"vaultboy": [], "success": []}
        self.current_animation   = "vaultboy"
        self.anim_start_time     = time.time()

        self.load_frames("frontend/frames/vaultboy", "vaultboy")
        self.load_frames("frontend/frames/success",  "success")

    # ── theme ─────────────────────────────────────────────────────────────────

    def cycle_theme(self):
        self.current_theme_index = (self.current_theme_index + 1) % len(self.theme_names)
        self.theme               = self.THEMES[self.theme_names[self.current_theme_index]]
        self.matrix_cols         = {}

    def get_color(self, color_name, dim=False):
        r, g, b = self._RGB.get(color_name, (255, 255, 255))
        if dim:
            r, g, b = int(r * .55), int(g * .55), int(b * .55)
        code = rgb(r, g, b)
        return lambda text: code + str(text) + RESET

    # ── animation ─────────────────────────────────────────────────────────────

    def load_frames(self, folder, key):
        if not os.path.isdir(folder):
            return
        all_files = [f for f in os.listdir(folder) if f.endswith(".png")]
        if not all_files:
            return
        if key == "vaultboy":
            files = sorted(all_files,
                           key=lambda f: int(f.replace("frame_", "").replace(".png", "")))
        else:
            files = sorted(all_files,
                           key=lambda f: int(f.rsplit("-", 1)[-1].replace(".png", "")))

        self.animations[key] = [
            Image.open(os.path.join(folder, f)).convert("RGB")
            for f in files
        ]

    def switch_animation(self, name):
        if name in self.animations:
            self.current_animation = name
            self.anim_start_time   = time.time()

    def get_frame(self):
        frames = self.animations.get(self.current_animation, [])
        if not frames:
            return None
        fps = 10
        idx = int((time.time() - self.anim_start_time) * fps)
        if self.current_animation == "success":
            if idx >= len(frames):
                self.switch_animation("vaultboy")
                return self.get_frame()
            return frames[idx]
        return frames[idx % len(frames)]

    # ── matrix rain ───────────────────────────────────────────────────────────

    def _init_matrix(self, width, height):
        for col in range(width):
            if col not in self.matrix_cols:
                self.matrix_cols[col] = {
                    "pos":   random.uniform(0, height),
                    "speed": random.uniform(0.3, 1.2),
                    "trail": random.randint(4, 20),
                    "chars": [random.choice(self._MATRIX_CHARS) for _ in range(max(height, 1))],
                }

    def _update_matrix(self, width, height):
        now = time.time()
        if now - self.matrix_last_update < 0.05:
            return
        self.matrix_last_update = now
        for col in range(width):
            c = self.matrix_cols[col]
            c["pos"] += c["speed"]
            if c["pos"] > height + c["trail"]:
                c["pos"]   = random.uniform(-c["trail"], 0)
                c["speed"] = random.uniform(0.3, 1.2)
                c["trail"] = random.randint(4, 20)
            if random.random() < 0.15:
                r = random.randint(0, height - 1)
                c["chars"][r] = random.choice(self._MATRIX_CHARS)

    def render_matrix(self, width, height):
        self._init_matrix(width, height)
        self._update_matrix(width, height)
        mr, mg, mb = self.theme.get("matrix", (0, 255, 65))

        screen = [[(" ", False)] * width for _ in range(height)]
        for row in range(height):
            for col in range(width):
                c    = self.matrix_cols[col]
                ch   = c["chars"][row % len(c["chars"])]
                head = int(c["pos"]) % max(height, 1)
                dist = (head - row) % max(height, 1)
                if dist == 0:
                    screen[row][col] = (rgb(255, 255, 255) + ch + RESET, False)
                elif dist < c["trail"]:
                    fade             = 1.0 - dist / c["trail"]
                    screen[row][col] = (
                        rgb(int(mr * fade), int(mg * fade), int(mb * fade)) + ch + RESET,
                        False,
                    )
        return screen

    # ── gif / halfblock panel ─────────────────────────────────────────────────

    def _render_halfblock(self, frame: Image.Image, cols: int, rows: int) -> list:
        if frame is None or cols < 1 or rows < 1:
            return [" " * cols] * rows

        target_w = cols
        target_h = rows * 2
        scale    = min(target_w / frame.width, target_h / frame.height)
        new_w    = max(1, int(frame.width  * scale))
        new_h    = max(2, int(frame.height * scale) // 2 * 2)

        frame  = frame.resize((new_w, new_h), Image.NEAREST)
        pixels = frame.load()
        ox     = (target_w - new_w) // 2
        oy     = (target_h - new_h) // 2 // 2

        lines = []
        for row in range(rows):
            line = []
            for col in range(cols):
                src_x = col - ox
                src_y = (row - oy) * 2

                def get_px(x, y):
                    if 0 <= x < new_w and 0 <= y < new_h:
                        return pixels[x, y]
                    return (0, 0, 0)

                tr, tg, tb  = get_px(src_x, src_y)
                br, bg_, bb = get_px(src_x, src_y + 1)
                line.append(rgb_bg(tr, tg, tb) + rgb(br, bg_, bb) + "▄" + RESET)
            lines.append("".join(line))
        return lines

    def gif_panel_render(self, cols: int, rows: int) -> list:
        frame = self.get_frame()
        if frame is None:
            return [" " * cols] * rows
        return self._render_halfblock(frame, cols, rows)

    # ── panel helpers ─────────────────────────────────────────────────────────

    def _blank_screen(self, width, height):
        return [[(" ", False)] * width for _ in range(height)]

    def _write_line(self, screen, row, col, text, width, color):
        for i, ch in enumerate(text):
            if col + i >= width:
                break
            screen[row][col + i] = (color(ch) if color else ch, False)

    # ── TLS inspect panel ─────────────────────────────────────────────────────

    def _tls_file_prompt_lines(self, inner):
        raw  = self.input_buffer
        full = expand_path(raw) if raw.strip() else ""

        if not raw.strip():
            check = "  (type a path — ~ and relative paths work)"
        elif os.path.isfile(full):
            check = "  ✓ file found"
        elif os.path.isdir(full):
            check = "  … directory — keep typing or press TAB"
        else:
            check = "  ✗ no such file"

        lines = [
            "  Path to host list file:",
            f"  > {raw[-(inner - 6):]}█",
            check,
        ]
        if self._path_error:
            lines.append(f"  ! {self._path_error}"[:inner])
        if self._path_matches:
            lines.append("")
            shown = self._path_matches[:6]
            for m in shown:
                lines.append(f"    {m}"[:inner])
            if len(self._path_matches) > len(shown):
                lines.append(f"    … +{len(self._path_matches) - len(shown)} more")
        lines += [
            "",
            f"  cwd: {os.getcwd()}"[:inner],
            "  TAB complete  |  ENTER start  |  ESC cancel",
        ]
        return lines

    def _tls_batch_lines(self, inner, height, used):
        b     = self.tls_batch
        res   = list(b["results"])          # snapshot; worker appends concurrently
        done  = len(res)
        total = max(1, b["total"])

        bar_w = max(10, inner - 16)
        fill  = int(bar_w * done / total)
        lines = [
            f"  File    : {os.path.basename(b['path'])}"[:inner],
            f"  [{'█' * fill}{'░' * (bar_w - fill)}] {done}/{b['total']}",
        ]
        if b["running"]:
            dots   = "." * (int(time.time() * 2) % 4)
            lines += [f"  Scanning: {b['current']}{dots}"[:inner]]
        else:
            ok   = sum(1 for r in res if not r.get("error"))
            lines += [f"  Done    : {ok} ok, {done - ok} failed"]

        # columns: domain | status | tls | expires/error
        st_w, tls_w = 10, 9
        dom_w = max(12, min(36, inner - 2 - st_w - tls_w - 14))
        lines += [
            "",
            f"  {'DOMAIN':<{dom_w}}{'STATUS':<{st_w}}{'TLS':<{tls_w}}EXPIRES / ERROR"[:inner],
        ]

        footer_rows = 6 if not b["running"] else 4
        visible     = max(1, height - used - len(lines) - footer_rows)
        max_scroll  = max(0, done - visible)
        b["scroll"] = min(b["scroll"], max_scroll)
        if b["running"]:
            b["scroll"] = max_scroll        # auto-follow while scanning

        for r in res[b["scroll"]:b["scroll"] + visible]:
            status = str(r.get("status") or ("ERROR" if r.get("error") else "?"))
            tail   = str(r.get("error") or r.get("expires") or "")
            lines.append(
                f"  {str(r.get('domain', '?'))[:dom_w - 1]:<{dom_w}}"
                f"{status[:st_w - 1]:<{st_w}}"
                f"{str(r.get('tls', '-'))[:tls_w - 1]:<{tls_w}}"
                f"{tail}"[:inner]
            )

        if not b["running"]:
            lines.append("")
            if b["out"]:
                lines.append(f"  Saved → {b['out']}"[-inner:])
            if done > visible:
                lines.append(f"  ↑/↓ scroll  ({b['scroll'] + 1}-{min(done, b['scroll'] + visible)} of {done})")
        return lines

    def render_tls_panel(self, width, height):
        screen = self._blank_screen(width, height)
        p      = self.tls_inspect_panel
        inner  = width - 4
        pad_x  = 2
        fc     = self.get_color(self.theme["feed"])
        b      = self.tls_batch

        if self.tls_batch_mode and b["running"]:
            status = f"BATCH  {len(b['results'])}/{b['total']}"
        elif self.tls_batch_mode and b["total"]:
            status = "BATCH COMPLETE"
        elif p and p.scanning:
            status = f"SCANNING  {p.host}..."
        elif p and p.scan_done and p.results:
            status = "COMPLETE"
        else:
            status = "READY"

        sep  = "═" * inner
        dash = "─" * inner

        lines = [
            sep,
            "TLS INSPECT".center(inner),
            sep,
            f"  Status  : {status}",
            dash,
        ]

        if self.active_input_mode == "tls_host":
            lines += [
                "  Enter domain to inspect:",
                f"  > {self.input_buffer}█",
                "",
                "  ENTER to scan  |  ESC to cancel",
                "  (press [F] instead to scan a file of hosts)",
            ]
        elif self.active_input_mode == "tls_file":
            lines += self._tls_file_prompt_lines(inner)
        elif self.tls_batch_mode and b["total"]:
            lines += self._tls_batch_lines(inner, height, len(lines))
        elif p and p.scanning:
            dots   = "." * (int(time.time() * 2) % 4)
            lines += [f"  Connecting{dots}"]
        elif p and p.scan_done and p.results:
            r     = p.results
            col_w = max(1, inner - 14)
            if r.get("error"):
                lines += ["  ERROR", f"  {r['error'][:inner - 4]}"]
            else:
                lines += [
                    f"  {'Domain':<10}: {str(r.get('domain',  '?'))[:col_w]}",
                    f"  {'Status':<10}: {str(r.get('status',  '?'))[:col_w]}",
                    f"  {'Issuer':<10}: {str(r.get('issuer',  '?'))[:col_w]}",
                    f"  {'Expires':<10}: {str(r.get('expires','?'))[:col_w]}",
                    f"  {'TLS':<10}: {str(r.get('tls',    '?'))[:col_w]}",
                    f"  {'Cipher':<10}: {str(r.get('cipher', '?'))[:col_w]}",
                ]
            lines += ["", "  [W] scan again  |  [F] scan file  |  [X] close"]
        else:
            lines += ["  Press [W] to scan a domain, [F] to scan a file"]

        lines += [
            dash,
            "  [W] Single  [F] File  [X] Close/Stop  [Q] Quit",
            sep,
        ]

        start_y = max(0, (height - len(lines)) // 2)
        for i, line in enumerate(lines):
            y = start_y + i
            if y >= height:
                break
            self._write_line(screen, y, pad_x, line[:inner], width, color=fc)

        return screen

    # ── web scraper panel ─────────────────────────────────────────────────────

    def render_scraper_panel(self, width, height):
        screen = self._blank_screen(width, height)
        p      = self.web_scraper_panel
        inner  = width - 4
        pad_x  = 2
        fc     = self.get_color(self.theme["feed"])

        if p and p.scanning:
            status = f"SCRAPING  {getattr(p, 'domain', '...')}..."
        elif self.web_scraper_state == 3:
            status = "COMPLETE"
        else:
            status = "READY"

        sep  = "═" * inner
        dash = "─" * inner

        lines = [
            sep,
            "WEB SCRAPER".center(inner),
            sep,
            f"  Status  : {status}",
            dash,
        ]

        if self.active_input_mode == "scraper_domain":
            lines += [
                "  Enter domain (without https://):",
                f"  > {self.input_buffer}█",
                "",
                "  ENTER to continue  |  ESC to cancel",
            ]
        elif self.active_input_mode == "scraper_filter_type":
            lines += [
                f"  Domain  : {self._scraper_domain}",
                "  Select filter type:",
                "",
                "    [1] Element   (e.g. h1, table, a, img)",
                "    [2] Images    (search by image filename/src)",
                "    [3] Keyword   (search by class name)",
                "",
                "  Press 1-3 to choose  |  ESC to cancel",
            ]
        elif self.active_input_mode == "scraper_flag":
            hint = self.PLACEHOLDER_HINTS.get(self._scraper_filter_key, "")
            lines += [
                f"  Domain  : {self._scraper_domain}",
                f"  Filter  : {self._scraper_filter_label}  ({hint})",
                "  Enter text to search for:",
                f"  > {self.input_buffer}█",
                "",
                "  ENTER to scrape  |  ESC to cancel",
            ]
        elif p and p.scanning:
            dots   = "." * (int(time.time() * 2) % 4)
            lines += [f"  Fetching page{dots}"]
        elif self.web_scraper_state == 3 and p and p.results:
            # ── results: only shown when state is explicitly 3 ──
            r     = p.results
            col_w = max(1, inner - 14)
            if r.get("error"):
                lines += ["  ERROR", f"  {r['error'][:inner - 4]}"]
            else:
                result       = str(r.get("result", "Not found"))
                result_lines = [result[i:i + col_w]
                                for i in range(0, min(len(result), col_w * 3), col_w)]
                lines += [
                    f"  {'Code':<10}: {r.get('status_code', '?')}",
                    f"  {'Engine':<10}: {r.get('engine',     '?')}",
                    f"  {'Result':<10}:",
                ]
                for rl in result_lines:
                    lines.append(f"    {rl}")
            lines += ["", "  [S] scrape again  |  [X] close"]
        elif self._scraper_domain and not self._scraper_filter_prompted:
            lines += ["  Fetching page..."]
        else:
            lines += ["  Press [S] to scrape a domain"]

        lines += [
            dash,
            "  [S] New scrape   [X] Close   [Q] Quit",
            sep,
        ]

        start_y = max(0, (height - len(lines)) // 2)
        for i, line in enumerate(lines):
            y = start_y + i
            if y >= height:
                break
            self._write_line(screen, y, pad_x, line[:inner], width, color=fc)

        return screen

    # ── main render ───────────────────────────────────────────────────────────

    def render(self):
        tw = self.term.width
        th = self.term.height

        right_w        = max(26, int(tw * 0.28))
        main_w         = tw - right_w - 1
        main_h         = th - 2
        feed_x         = main_w + 1
        stats_h        = 6
        feed_h         = th - stats_h - 7
        stats_y        = feed_h + 1
        left_inner_w   = main_w - 2
        left_inner_h   = main_h
        matrix_inner_h = max(1, left_inner_h - 2)

        fc = self.get_color(self.theme["feed"])
        sc = self.get_color(self.theme["stats"])
        mc = self.get_color(self.theme["feed"], dim=True)

        out = ["\033[?25l", self.term.home]

        # ── left panel border ─────────────────────────────────────────────────
        if self.tls_inspect_mode:
            left_title = " TLS Inspect "
        elif self.web_scraper_mode:
            left_title = " Web Scraper "
        else:
            left_title = " Matrix "

        top_dash = "─" * (main_w - len(left_title) - 2)
        out.append(self.term.move(0, 0) + fc("┌" + left_title + top_dash + "┐"))

        for y in range(1, main_h + 1):
            out.append(self.term.move(y, 0)          + fc("│"))
            out.append(self.term.move(y, main_w - 1) + fc("│"))

        out.append(self.term.move(main_h + 1, 0) + fc("└" + "─" * (main_w - 2) + "┘"))

        # ── left panel content ────────────────────────────────────────────────
        if self.tls_inspect_mode:
            left_screen = self.render_tls_panel(left_inner_w, left_inner_h)
        elif self.web_scraper_mode:
            left_screen = self.render_scraper_panel(left_inner_w, left_inner_h)
        else:
            left_screen = self.render_matrix(left_inner_w, matrix_inner_h)

        for y, row in enumerate(left_screen):
            if y >= left_inner_h:
                break
            line = []
            for cell in row:
                line.append(cell[0] if isinstance(cell, tuple) else cell)
            out.append(self.term.move(y + 1, 1) + "".join(line))

        # ── gif panel ─────────────────────────────────────────────────────────
        gif_inner_w = right_w - 2
        gif_inner_h = feed_h  - 1

        gif_title = " Vault Boy "
        gif_fill  = "─" * (right_w - len(gif_title) - 2)
        out.append(self.term.move(0,      feed_x) + fc("┌" + gif_title + gif_fill + "┐"))
        out.append(self.term.move(feed_h, feed_x) + fc("└" + "─" * (right_w - 2) + "┘"))

        for y in range(1, feed_h):
            out.append(self.term.move(y, feed_x)               + fc("│"))
            out.append(self.term.move(y, feed_x + right_w - 1) + fc("│"))

        for y, row_str in enumerate(self.gif_panel_render(gif_inner_w, gif_inner_h)):
            out.append(self.term.move(y + 1, feed_x + 1) + row_str)

        # ── stats panel ───────────────────────────────────────────────────────
        st_title = f" Stats — {self.theme['name'].upper()} "
        st_fill  = "─" * (right_w - len(st_title) - 2)
        out.append(self.term.move(stats_y, feed_x) + sc("┌" + st_title + st_fill + "┐"))
        out.append(self.term.move(th - 1,  feed_x) + sc("└" + "─" * (right_w - 2) + "┘"))

        for y in range(stats_y + 1, th - 1):
            out.append(self.term.move(y, feed_x)               + sc("│"))
            out.append(self.term.move(y, feed_x + right_w - 1) + sc("│"))

        try:
            local_ip = socket.gethostbyname(socket.gethostname())
        except Exception:
            local_ip = "unknown"
        try:
            mac = ":".join(f"{(uuid.getnode() >> (8*i)) & 0xff:02x}" for i in range(5, -1, -1))
        except Exception:
            mac = "unknown"

        elapsed     = int(time.time() - self.start_time)
        h, rem      = divmod(elapsed, 3600)
        m, s        = divmod(rem, 60)
        stats_inner = right_w - 4

        b = self.tls_batch
        tls_stat = (
            f"batch {len(b['results'])}/{b['total']}" if b["running"] else
            "scanning" if (self.tls_inspect_panel and self.tls_inspect_panel.scanning) else
            "done"     if (self.tls_inspect_panel and self.tls_inspect_panel.scan_done) else
            "idle"
        )
        scraper_stat = (
            "scanning" if (self.web_scraper_panel and self.web_scraper_panel.scanning) else
            "done"     if (self.web_scraper_state == 3) else
            "idle"
        )

        stat_lines = [
            f"IP      : {local_ip}",
            f"MAC     : {mac}",
            f"Uptime  : {h:02d}:{m:02d}:{s:02d}",
            f"Anim    : {self.current_animation}",
            "─" * stats_inner,
            f"TLS     : {tls_stat}",
            f"Scraper : {scraper_stat}"
        ]

        for i, line in enumerate(stat_lines):
            y = stats_y + 2 + i
            if y >= th - 2:
                break
            out.append(
                self.term.move(y, feed_x + 2) +
                sc(line[:stats_inner].ljust(stats_inner))
            )

        # ── legend bar ────────────────────────────────────────────────────────
        legend    = " [W]TLS  [F]TLS File  [S]Scrape  [T]Theme  [C]Legend  [Q]Quit"
        st_txt    = "PAUSED" if self.paused else "LIVE"
        st_col    = self.get_color("bright_red") if self.paused else self.get_color("bright_green")
        bar_inner = main_w - 2

        if self.show_legend:
            out.append(self.term.move(main_h, 1) + fc(legend[:bar_inner].center(bar_inner)))
        else:
            tag    = f" {st_txt} "
            rest_w = max(0, bar_inner - len(tag))
            out.append(
                self.term.move(main_h, 1) +
                st_col(tag) +
                mc(legend[:rest_w].ljust(rest_w))
            )

        out.append(self.term.move(th - 1, tw - 1) + "\033[?25l")
        sys.stdout.write("".join(out))
        sys.stdout.flush()

    # ── path tab-completion ───────────────────────────────────────────────────

    def _complete_path(self):
        raw      = self.input_buffer
        expanded = os.path.expanduser(raw) if raw else "./"
        matches  = sorted(glob.glob(glob.escape(expanded) + "*"))
        self._path_error = ""

        if not matches:
            self._path_matches = []
            return

        if len(matches) == 1:
            completed = matches[0]
            if os.path.isdir(completed):
                completed = completed.rstrip(os.sep) + os.sep
            self._path_matches = []
        else:
            completed = os.path.commonprefix(matches)
            self._path_matches = [
                os.path.basename(m.rstrip(os.sep)) + (os.sep if os.path.isdir(m) else "")
                for m in matches
            ]

        # keep the ~ the user typed instead of expanding it in the buffer
        home = os.path.expanduser("~")
        if raw.startswith("~") and completed.startswith(home):
            completed = "~" + completed[len(home):]
        self.input_buffer = completed

    # ── input handling ────────────────────────────────────────────────────────

    def handle_input(self):
        with self.term.cbreak():
            while self.running:
                key = self.term.inkey(timeout=0.05)
                if not key:
                    continue

                k = str(key).lower()

                # ── text input intercept ──────────────────────────────────────
                if self.active_input_mode is not None:

                    # filter-type screen is a single-keypress menu (1-3), not free text
                    if self.active_input_mode == "scraper_filter_type":
                        if k in self.FILTER_TEMPLATES:
                            filter_key, template          = self.FILTER_TEMPLATES[k]
                            self._scraper_filter_key      = filter_key
                            self._scraper_filter_template = template
                            self._scraper_filter_label    = filter_key.capitalize()
                            self.input_buffer      = ""
                            self.active_input_mode = "scraper_flag"
                        elif key.code == self.term.KEY_ESCAPE:
                            self.active_input_mode = None
                            self.input_buffer      = ""
                            self._scraper_domain   = ""
                        continue

                    # TAB completes paths in the file prompt
                    if self.active_input_mode == "tls_file" and (
                            key.code == self.term.KEY_TAB or str(key) == "\t"):
                        self._complete_path()
                        continue

                    if key.code == self.term.KEY_ENTER:
                        self._commit_input()
                    elif key.code == self.term.KEY_BACKSPACE or key.code == self.term.KEY_DELETE:
                        self.input_buffer  = self.input_buffer[:-1]
                        self._path_matches = []
                        self._path_error   = ""
                    elif key.code == self.term.KEY_ESCAPE:
                        if self.active_input_mode == "tls_file":
                            self.tls_inspect_mode = False
                        self.active_input_mode = None
                        self.input_buffer      = ""
                        self._path_matches     = []
                        self._path_error       = ""
                    elif not key.is_sequence:
                        self.input_buffer += str(key)
                        self._path_matches = []
                        self._path_error   = ""
                    continue

                # ── batch results scrolling ───────────────────────────────────
                if self.tls_inspect_mode and self.tls_batch_mode:
                    b = self.tls_batch
                    if key.code == self.term.KEY_UP:
                        b["scroll"] = max(0, b["scroll"] - 1); continue
                    if key.code == self.term.KEY_DOWN:
                        b["scroll"] += 1; continue
                    if key.code == self.term.KEY_PGUP:
                        b["scroll"] = max(0, b["scroll"] - 10); continue
                    if key.code == self.term.KEY_PGDOWN:
                        b["scroll"] += 10; continue

                # ── hotkeys ───────────────────────────────────────────────────
                if k == "q" or key.code == self.term.KEY_ESCAPE:
                    self.running = False
                elif key == " ":
                    self.paused = not self.paused
                elif k == "t":
                    self.cycle_theme()
                elif k == "c":
                    self.show_legend = not self.show_legend
                elif k == "x":
                    self._close_all_panels()
                elif k == "w":
                    self._open_tls()
                elif k == "f":
                    self._open_tls_file()
                elif k == "s":
                    self._open_scraper()

    # ── panel open / close ────────────────────────────────────────────────────

    def _stop_tls_batch(self):
        self.tls_batch["stop"] = True
        self.tls_batch_mode    = False

    def _close_all_panels(self):
        self._stop_tls_batch()
        self.tls_inspect_mode  = False
        self.web_scraper_mode  = False
        self.ip_scan_mode      = False
        self.tls_inspect_state = 0
        self.web_scraper_state = 0
        self.active_input_mode = None
        self.input_buffer      = ""
        self._scraper_domain   = ""
        self._path_matches     = []
        self._path_error       = ""

        self._scraper_filter_key      = None
        self._scraper_filter_template = None
        self._scraper_filter_label    = None
        self._scraper_filter_prompted = False
        self._scraper_search_started  = False

        if self.tls_inspect_panel:
            self.tls_inspect_panel.scan_done = False
            self.tls_inspect_panel.scanning  = False
            self.tls_inspect_panel.results   = {}
        if self.web_scraper_panel:
            self.web_scraper_panel.scan_done = False
            self.web_scraper_panel.scanning  = False
            self.web_scraper_panel.results   = {}

    def _open_tls(self):
        self._stop_tls_batch()
        self.tls_inspect_mode  = True
        self.web_scraper_mode  = False
        self.ip_scan_mode      = False
        self.tls_inspect_state = 1
        self.active_input_mode = "tls_host"
        self.input_buffer      = ""
        if self.tls_inspect_panel:
            self.tls_inspect_panel.scan_done = False
            self.tls_inspect_panel.results   = {}

    def _open_tls_file(self):
        if self.tls_batch["running"]:
            # a batch is already going — just bring its panel back up
            self.tls_inspect_mode = True
            self.web_scraper_mode = False
            self.tls_batch_mode   = True
            return
        self.tls_inspect_mode  = True
        self.web_scraper_mode  = False
        self.ip_scan_mode      = False
        self.tls_inspect_state = 1
        self.active_input_mode = "tls_file"
        self.input_buffer      = self._last_batch_path   # pre-fill last used path
        self._path_matches     = []
        self._path_error       = ""

    def _open_scraper(self):
        self._stop_tls_batch()
        self.web_scraper_mode  = True
        self.tls_inspect_mode  = False
        self.ip_scan_mode      = False
        self.web_scraper_state = 1
        self.active_input_mode = "scraper_domain"
        self.input_buffer      = ""
        self._scraper_domain   = ""

        self._scraper_filter_key      = None
        self._scraper_filter_template = None
        self._scraper_filter_label    = None
        self._scraper_filter_prompted = False
        self._scraper_search_started  = False

        if self.web_scraper_panel:
            self.web_scraper_panel.scan_done  = False
            self.web_scraper_panel.fetch_done = False
            self.web_scraper_panel.results    = {}

    # ── TLS batch ─────────────────────────────────────────────────────────────

    @staticmethod
    def _new_batch_state():
        return {
            "running": False, "stop": False, "path": "", "out": "",
            "total": 0, "current": "", "results": [], "scroll": 0,
        }

    def _start_tls_batch(self, raw_path):
        """Validate the path and kick off the worker. Returns an error string or ''."""
        if not self.tls_inspect_panel:
            return "TLS module not loaded"
        path = expand_path(raw_path)
        if not os.path.isfile(path):
            return f"not a file: {path}"
        try:
            targets = load_tls_targets(path)
        except OSError as e:
            return str(e)
        if not targets:
            return "no hosts found in file"

        self._last_batch_path = raw_path
        b = self._new_batch_state()           # fresh dict so an old worker can't touch it
        b.update(running=True, path=path, total=len(targets))
        self.tls_batch         = b
        self.tls_batch_mode    = True
        self.tls_inspect_state = 4
        Thread(target=self._run_tls_batch, args=(b, targets), daemon=True).start()
        return ""

    def _run_tls_batch(self, b, targets):
        p = self.tls_inspect_panel
        for host in targets:
            if b["stop"] or not self.running:
                break
            b["current"] = host
            p.scan_done  = False
            p.results    = {}
            try:
                p.start(host)                 # your backend; blocking or not, both work
                t0 = time.time()
                while (not p.scan_done and not b["stop"] and self.running
                       and time.time() - t0 < self.TLS_BATCH_TIMEOUT):
                    time.sleep(0.1)
                res = dict(p.results or {})
                if not res:
                    res = {"status": "ERROR", "error": "timeout / no result"}
            except Exception as e:
                res = {"status": "ERROR", "error": str(e)}
            res.setdefault("domain", host)
            b["results"].append(res)

        b["running"] = False
        b["current"] = ""
        if b["results"]:
            b["out"] = self._export_tls_batch(b)
        if not b["stop"]:
            self.switch_animation("success")

    def _export_tls_batch(self, b):
        base  = os.path.splitext(b["path"])[0]
        stamp = datetime.now().strftime("%Y%m%d-%H%M%S")
        out   = f"{base}_tls_{stamp}.csv"
        keys  = ["domain", "status", "issuer", "expires", "tls", "cipher", "error"]
        try:
            with open(out, "w", newline="", encoding="utf-8") as f:
                w = csv.DictWriter(f, fieldnames=keys, extrasaction="ignore")
                w.writeheader()
                w.writerows(b["results"])
            return out
        except OSError as e:
            return f"(CSV save failed: {e})"

    # ── commit input ──────────────────────────────────────────────────────────

    def _commit_input(self):
        val  = self.input_buffer.strip()
        mode = self.active_input_mode
        self.input_buffer      = ""
        self.active_input_mode = None

        if mode == "tls_host":
            if val and self.tls_inspect_panel:
                self.tls_inspect_state = 2
                Thread(target=self.tls_inspect_panel.start, args=(val,), daemon=True).start()

        elif mode == "tls_file":
            err = self._start_tls_batch(val) if val else "enter a file path"
            if err:
                # stay on the prompt, keep what they typed
                self._path_error       = err
                self.input_buffer      = val
                self.active_input_mode = "tls_file"
            else:
                self._path_error   = ""
                self._path_matches = []

        elif mode == "scraper_domain":
            if val and self.web_scraper_panel:
                self._scraper_domain   = val
                self.web_scraper_state = 2
                self.active_input_mode = None
                self.web_scraper_panel.start_fetch(val)
            else:
                self.active_input_mode = "scraper_domain"

        elif mode == "scraper_flag":
            if self._scraper_domain and self.web_scraper_panel:
                template     = self._scraper_filter_template or "{value}"
                final_filter = template.format(value=val)
                # reset scan_done so _watch_tools can detect search completion
                self.web_scraper_panel.scan_done = False
                self.web_scraper_panel.results   = {}
                self._scraper_search_started     = True
                self.web_scraper_state           = 2
                self.web_scraper_panel.start_search(final_filter)

            # always clear filter key after committing
            self._scraper_filter_key      = None
            self._scraper_filter_template = None
            self._scraper_filter_label    = None

    # ── watch for tool completion ─────────────────────────────────────────────

    def _watch_tools(self):
        while self.running:
            time.sleep(0.2)

            # (batch mode uses tls_inspect_state == 4, so this ignores it)
            tls = self.tls_inspect_panel
            if tls and tls.scan_done and self.tls_inspect_state == 2:
                self.tls_inspect_state = 3
                self.switch_animation("success")

            ws = self.web_scraper_panel
            if ws and self.web_scraper_mode and self.web_scraper_state == 2:
                fetch_done = getattr(ws, "fetch_done", False)

                # Phase 1: fetch finished → show filter prompt (only once, only if
                # the search has not started yet)
                if (fetch_done
                        and not self._scraper_filter_prompted
                        and not self._scraper_search_started
                        and self.active_input_mode is None):
                    self._scraper_filter_prompted = True
                    self.active_input_mode = "scraper_filter_type"

                # Phase 2: search finished → lock on results
                elif (self._scraper_search_started
                        and ws.scan_done
                        and self.active_input_mode is None):
                    self._scraper_search_started = False
                    self.web_scraper_state       = 3
                    self.switch_animation("success")

    # ── run ───────────────────────────────────────────────────────────────────

    def run(self):
        Thread(target=self.handle_input, daemon=True).start()
        Thread(target=self._watch_tools, daemon=True).start()

        sys.stdout.write("\033[?25l\033[2J\033[H")
        sys.stdout.flush()

        with self.term.fullscreen(), self.term.hidden_cursor():
            try:
                while self.running:
                    t0    = time.time()
                    self.render()
                    sleep = max(0, 0.05 - (time.time() - t0))
                    if sleep:
                        time.sleep(sleep)
            except KeyboardInterrupt:
                pass
            finally:
                self.running = False
                sys.stdout.write("\033[?25h")
                sys.stdout.flush()
