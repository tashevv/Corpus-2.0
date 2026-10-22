"""
Offline mode for Corpus
=======================

A window (opened with the "Offline mode" button next to "Coverage") that fills the local caches for
one language so the app keeps working without internet:

* definitions   -> data/lang/<code>/dictionary.db, table `entries`   (freedictionaryapi.com)
* translations  -> the same database, table `translations`           (Translator, any provider)
* speech        -> data/lang/tts/<sha1>.mp3                          (Google TTS, same cache as Speaker)

It is the multi-language version of crawl_ru.py: resumable, rate limited (sliding one-hour window
seeded from the database) and safe to stop at any time, because every result is saved at once.

"Auto cache check" re-scans what is cached (and repairs what is broken: unparsable definitions,
empty audio files) whenever the language / target / range changes and after every crawl.
The crawl itself always skips whatever is already cached.

Everything that belongs to the main script (data sets, Translator, build_blocks, tts helpers, palette)
is reached through the `host` module that corpus.py passes in, so this file never imports corpus.py.
"""
from __future__ import annotations

import json
import os
import re
import threading
import time
import tkinter as tk
import urllib.error
import urllib.parse
import urllib.request
from collections import deque
from dataclasses import dataclass
from tkinter import messagebox, ttk

TTS_SCOPES = ("Words only", "Words + examples", "Words + all texts")
LABELS = {"defs": "Definitions", "tr": "Translation", "tts": "Speech"}
MAX_FAILS = 6          # failures in a row before a service is switched off for the rest of the run


# --------------------------------------------------------------------------- small helpers
def fmt_dur(sec: float) -> str:
    sec = int(max(sec, 0))
    d, rem = divmod(sec, 86400)
    h, rem = divmod(rem, 3600)
    m, s = divmod(rem, 60)
    if d:
        return f"{d}d {h}h {m}m"
    if h:
        return f"{h}h {m}m"
    return f"{m}m {s}s"


def fmt_bytes(n: float) -> str:
    for unit in ("B", "KB", "MB", "GB"):
        if n < 1024 or unit == "GB":
            return f"{n:.0f} {unit}" if unit == "B" else f"{n:.1f} {unit}"
        n /= 1024
    return f"{n:.1f} GB"


@dataclass
class Options:
    code: str
    tl: str                         # translation target language code
    do_defs: bool = True
    do_trans: bool = True
    do_tts: bool = False
    tts_scope: int = 0              # index into TTS_SCOPES
    start: int = 1
    end: int | None = None
    flagged_only: bool = False
    retry_404: bool = False
    defs_per_hour: int = 950
    tr_delay: float = 0.3
    tts_delay: float = 0.8
    provider: str = "Auto"


# --------------------------------------------------------------------------- what needs caching
def select_words(entries, flags: set, o: Options) -> list[tuple[int, str]]:
    end = o.end or len(entries)
    return [(e.rank, e.word) for e in entries
            if o.start <= e.rank <= end and (not o.flagged_only or e.word in flags)]


def entry_blocks(h, body: str, lang: str):
    """(valid, blocks). `valid` is False only when the stored body is not parsable JSON."""
    try:
        data = json.loads(body)
    except ValueError:
        return False, []
    try:
        return True, h.build_blocks(data, lang)
    except Exception:           # odd data shape: no blocks, but the entry itself is not "corrupt"
        return True, []


def needed_keys(h, word: str, blocks, sl: str, tl: str) -> list[str]:
    """Cache keys Translator uses for the word and for every translatable block (see Translator)."""
    keys = [h.Translator._key("w", sl, word)]
    for b in blocks:
        if b.translate and b.text.strip() and b.lang != tl:
            keys.append(h.Translator._key("t", b.lang, " ".join(b.text.split())))
    return keys


def speech_items(word: str, wlang: str, blocks, scope: int) -> list[tuple[str, str]]:
    """(language, text) pairs to pre-generate: the headword and, optionally, the clickable texts."""
    items = [(wlang, word)]
    if scope:
        for b in blocks:
            if not b.speak or (scope == 1 and b.kind != "example"):
                continue
            t = b.text.strip()
            if t:
                items.append((b.lang, t))
    return items


def db_statuses(store) -> dict[str, int]:
    with store.lock:
        return {w: s for w, s in store.conn.execute("SELECT word, status FROM entries")}


def db_tr_keys(store, tl: str) -> set[str]:
    with store.lock:
        return {r[0] for r in store.conn.execute("SELECT key FROM translations WHERE tl=?", (tl,))}


def tts_listing(tts_dir) -> dict[str, int]:
    """{file name: size} of the non-empty .mp3 files in the speech cache."""
    out: dict[str, int] = {}
    try:
        with os.scandir(tts_dir) as it:
            for e in it:
                if e.name.endswith(".mp3"):
                    try:
                        size = e.stat().st_size
                    except OSError:
                        continue
                    if size > 0:
                        out[e.name] = size
    except OSError:
        pass
    return out


def scan_cache(h, store, ds, words, tl: str, tts_scope: int, stop: threading.Event, progress=None):
    """Count what is cached for `words`. Returns a dict, or None if `stop` was set."""
    sl = ds.lang
    statuses = db_statuses(store)
    tr_keys = db_tr_keys(store, tl)
    files = tts_listing(h.TTS_DIR)
    res = dict(total=len(words), defs_ok=0, defs_404=0, defs_missing=0, defs_corrupt=0,
               tr_complete=0, tr_partial=0, tr_none=0,
               tts_words=0, tts_extra_have=0, tts_extra_total=0, tts_bytes=0)
    extra_seen: set[str] = set()
    for i, (_rank, word) in enumerate(words, 1):
        if stop.is_set():
            return None
        st = statuses.get(word)
        blocks, valid = [], True
        if st == 200:
            row = store.get_entry(word)
            valid, blocks = entry_blocks(h, row[1], sl) if row else (False, [])
            res["defs_ok" if valid else "defs_corrupt"] += 1
        elif st == 404:
            res["defs_404"] += 1
        else:
            res["defs_missing"] += 1

        have = [k in tr_keys for k in needed_keys(h, word, blocks, sl, tl)]
        known = st == 404 or (st == 200 and valid)
        if known and all(have):
            res["tr_complete"] += 1
        elif any(have):
            res["tr_partial"] += 1
        else:
            res["tr_none"] += 1

        for n, (lang, text) in enumerate(speech_items(word, sl, blocks, tts_scope)):
            name = h.tts_path(lang, text).name
            if n == 0:
                if name in files:
                    res["tts_words"] += 1
                    res["tts_bytes"] += files[name]
            elif name not in extra_seen:
                extra_seen.add(name)
                res["tts_extra_total"] += 1
                if name in files:
                    res["tts_extra_have"] += 1
                    res["tts_bytes"] += files[name]
        if progress and i % 500 == 0:
            progress(i, len(words))
    return res


# --------------------------------------------------------------------------- definitions download
def fetch_definition(h, word: str, dict_lang: str):
    """(http_status, body, retry_after). Network errors propagate as URLError / OSError."""
    url = h.DICT_URL.format(lang=dict_lang, word=urllib.parse.quote(word, safe=""))
    req = urllib.request.Request(url, headers={"User-Agent": h.USER_AGENT, "Accept": "application/json"})
    try:
        with urllib.request.urlopen(req, timeout=30) as resp:
            return resp.status, resp.read().decode("utf-8"), None
    except urllib.error.HTTPError as e:
        return e.code, e.read().decode("utf-8", "replace"), e.headers.get("Retry-After")


class RateLimiter:
    """Sliding window: at most `limit` requests in any `per` seconds. Waiting can be interrupted."""

    def __init__(self, limit: int, per: float = 3600.0):
        self.limit, self.per = max(1, int(limit)), per
        self.stamps: deque[float] = deque()

    def seed(self, stores) -> int:
        """Count requests of the last hour already stored (the API limit is per IP, not per data set)."""
        now_wall, now_mono = time.time(), time.monotonic()
        stamps: list[float] = []
        for store in stores:
            try:
                with store.lock:
                    rows = store.conn.execute(
                        "SELECT CAST(strftime('%s', fetched_at) AS INTEGER) FROM entries "
                        "WHERE fetched_at >= datetime('now', '-1 hour')").fetchall()
            except Exception:
                continue
            stamps += [now_mono - max(now_wall - ts, 0) for (ts,) in rows if ts is not None]
        self.stamps = deque(sorted(stamps))
        return len(self.stamps)

    def acquire(self, stop: threading.Event, log) -> bool:
        """Block until a request is allowed and record it. False if `stop` was set while waiting."""
        while not stop.is_set():
            now = time.monotonic()
            while self.stamps and now - self.stamps[0] >= self.per:
                self.stamps.popleft()
            if len(self.stamps) < self.limit:
                self.stamps.append(now)
                return True
            wait = self.per - (now - self.stamps[0]) + 1
            log(f"Hourly budget of {self.limit} used up — waiting {fmt_dur(wait)} "
                f"(resumes about {time.strftime('%H:%M', time.localtime(time.time() + wait))})")
            if stop.wait(wait):
                return False
        return False

    def penalize(self, seconds: float) -> None:
        """After a 429 the server counts more requests than we do: fill the window for `seconds`."""
        fake = time.monotonic() - self.per + seconds
        while len(self.stamps) < self.limit:
            self.stamps.appendleft(fake)
        self.stamps = deque(sorted(self.stamps))


# --------------------------------------------------------------------------- the crawler
class Crawler(threading.Thread):
    """Walks the selected words and, for each, completes definitions -> translation -> speech.

    Already cached items cost nothing, so a stopped or repeated crawl simply continues. Only the
    definitions are limited per hour; translation and speech use a short pause between requests.
    A service that fails MAX_FAILS times in a row is switched off for the rest of the run.
    """

    def __init__(self, host, store, ds, words, opts: Options, emit, stores):
        super().__init__(daemon=True, name="offline-crawler")
        self.h, self.store, self.ds, self.words, self.o = host, store, ds, words, opts
        self.emit, self.stores = emit, stores
        self.stop_event = threading.Event()
        self.stats = dict(words=0, defs=0, nf=0, fixed=0, tr=0, tts=0, errors=0)
        self.fails = {"defs": 0, "tr": 0, "tts": 0}
        self.off: set[str] = set()
        self.limiter: RateLimiter | None = None
        self._last_emit = 0.0

    # -- plumbing
    def log(self, msg: str):
        self.emit("log", msg)

    def _sleep(self, sec: float) -> bool:
        """Interruptible sleep; False if the crawl was stopped meanwhile."""
        if sec <= 0:
            return not self.stop_event.is_set()
        return not self.stop_event.wait(sec)

    def _on(self, svc: str) -> bool:
        wanted = {"defs": self.o.do_defs, "tr": self.o.do_trans, "tts": self.o.do_tts}[svc]
        return wanted and svc not in self.off

    def _fail(self, svc: str, what, exc, sleep: bool = True):
        self.fails[svc] += 1
        self.stats["errors"] += 1
        n = self.fails[svc]
        self.log(f"{LABELS[svc]} failed for “{str(what)[:40]}”: {exc}")
        if n >= MAX_FAILS:
            self.off.add(svc)
            self.log(f"{LABELS[svc]} switched off for the rest of this run ({n} failures in a row).")
        elif sleep:
            self._sleep(min(300.0, 10.0 * 2 ** (n - 1)))

    def _progress(self, n: int, total: int, rank: int, word: str):
        now = time.monotonic()
        if n == total or now - self._last_emit >= 0.25:
            self._last_emit = now
            self.emit("progress", n, total, rank, word, dict(self.stats))

    # -- main loop
    def run(self):
        t0 = time.time()
        try:
            self._crawl()
        except Exception as e:
            self.log(f"Crawl stopped by an error: {type(e).__name__}: {e}")
        self.emit("done", dict(self.stats), time.time() - t0, self.stop_event.is_set())

    def _crawl(self):
        o, total = self.o, len(self.words)
        translator = None
        if o.do_trans:
            translator = self.h.Translator(self.store)      # own instance: own provider cool-downs
            translator.mode = o.provider
        seeded = 0
        if o.do_defs:
            self.limiter = RateLimiter(o.defs_per_hour)
            seeded = self.limiter.seed(self.stores)
        todo = [name for name, on in (("definitions", o.do_defs), ("translations", o.do_trans),
                                      ("speech", o.do_tts)) if on]
        self.log(f"Starting: {total:,} words, {', '.join(todo)}."
                 + (f" {seeded} definition requests already counted in the last hour (budget "
                    f"{o.defs_per_hour}/h)." if o.do_defs else ""))
        for n, (rank, word) in enumerate(self.words, 1):
            if self.stop_event.is_set():
                break
            if not any(self._on(s) for s in ("defs", "tr", "tts")):
                self.log("Every selected service has been switched off — stopping.")
                break
            self._word(word, translator)
            self.stats["words"] = n
            self._progress(n, total, rank, word)

    def _word(self, word: str, translator):
        o, h, store, sl = self.o, self.h, self.store, self.ds.lang

        # 1) definitions
        row = store.get_entry(word)
        blocks, corrupt = [], False
        if row and row[0] == 200:
            ok, blocks = entry_blocks(h, row[1], sl)
            corrupt = not ok
        if self._on("defs") and (row is None or corrupt or (row[0] == 404 and o.retry_404)):
            res = self._fetch_defs(word)
            if res is not None:
                status, body = res
                store.put_entry(word, status, body)
                row = res
                self.stats["fixed"] += int(corrupt)
                self.stats["defs" if status == 200 else "nf"] += 1
                blocks = entry_blocks(h, body, sl)[1] if status == 200 else []

        # 2) translation of the word and of every translatable block
        if self._on("tr") and translator is not None:
            keys = needed_keys(h, word, blocks, sl, o.tl)
            if any(store.get_translation(k, o.tl) is None for k in keys):
                if not self._sleep(o.tr_delay):
                    return
                try:
                    translator.word(word, o.tl, False, sl)
                    translator.blocks(blocks, o.tl, False)
                    self.stats["tr"] += 1
                    self.fails["tr"] = 0
                except Exception as e:
                    self._fail("tr", word, e)

        # 3) speech
        if self._on("tts"):
            for lang, text in speech_items(word, sl, blocks, o.tts_scope):
                if self.stop_event.is_set() or not self._on("tts"):
                    return
                path = h.tts_path(lang, text)
                try:
                    if path.exists() and path.stat().st_size > 0:
                        continue
                except OSError:
                    pass
                if not self._sleep(o.tts_delay):
                    return
                try:
                    if h.tts_fetch(lang, text, self.stop_event.is_set) is not None:
                        self.stats["tts"] += 1
                        self.fails["tts"] = 0
                except Exception as e:
                    self._fail("tts", text, e)

    def _fetch_defs(self, word: str):
        """(status, body) to store, or None to skip the word for this run."""
        delay = 5.0
        for attempt in range(1, 6):
            if not self.limiter.acquire(self.stop_event, self.log):
                return None
            try:
                status, body, retry_after = fetch_definition(self.h, word, self.ds.dict_lang)
            except (urllib.error.URLError, OSError, TimeoutError) as e:
                self.log(f"  network error for “{word}” ({e}); retry {attempt}/5 in {int(delay)}s")
                if not self._sleep(delay):
                    return None
                delay = min(delay * 2, 300)
                continue
            if status == 404:
                self.fails["defs"] = 0
                return status, body
            if status == 200:
                try:
                    json.loads(body)
                except ValueError:
                    self.log(f"  invalid JSON for “{word}”; retry {attempt}/5")
                    if not self._sleep(delay):
                        return None
                    delay = min(delay * 2, 300)
                    continue
                self.fails["defs"] = 0
                return status, body
            if status == 429:
                try:
                    wait = max(float(retry_after), 60.0) if retry_after else 600.0
                except ValueError:
                    wait = 600.0
                self.log(f"  HTTP 429 (rate limit) — pausing {fmt_dur(wait)}")
                self.limiter.penalize(wait)
                if not self._sleep(wait):
                    return None
                continue
            self.log(f"  HTTP {status} for “{word}”; retry {attempt}/5 in {int(delay)}s")
            if not self._sleep(delay):
                return None
            delay = min(delay * 2, 300)
        self._fail("defs", word, "gave up after 5 attempts", sleep=False)
        return None


# --------------------------------------------------------------------------- the window
class OfflineWindow:
    def __init__(self, app, host):
        self.app, self.h = app, host
        self.crawler: Crawler | None = None
        self.entries: list = []
        self.store = None
        self.code = app.code
        self.ds = host.DATASETS[self.code]
        self.targets: list = []
        self.target_by_label: dict = {}
        self._scan_token = 0
        self._scan_stop = threading.Event()
        self._scan_after = None
        self._bars: dict = {}
        self.saved: dict = host.load_offline_settings()
        self._loading = True            # don't write settings while the widgets are being set up
        self._geo_job = None

        C = host.C
        self.win = win = tk.Toplevel(app)
        win.title("Offline mode — cache a language for offline use")
        win.configure(bg=C["bg"])
        win.geometry(host.fit_geometry(win, self.saved.get("geometry"), "800x820"))
        win.minsize(720, 680)
        win.transient(app)
        win.protocol("WM_DELETE_WINDOW", self.close)
        win.bind("<Configure>", self._on_configure)
        self._build()
        self._set_language(self.code)
        self._loading = False

    def alive(self) -> bool:
        return bool(self.win.winfo_exists())

    # ------------------------------------------------------------------ layout
    def _build(self):
        h, win = self.h, self.win
        C = h.C
        s = self.saved
        style = ttk.Style(win)
        style.configure("Cache.Horizontal.TProgressbar", troughcolor=C["input"], background=C["accent"],
                    bordercolor=C["border"], lightcolor=C["accent"], darkcolor=C["accent"], thickness=14)

        outer = ttk.Frame(win, padding=16)
        outer.pack(fill="both", expand=True, padx=10, pady=10)
        outer.columnconfigure(0, weight=1)
        outer.rowconfigure(9, weight=1)

        # --- language
        ttk.Label(outer, text="LANGUAGE", style="Section.TLabel").grid(row=0, column=0, sticky="w")
        f = ttk.Frame(outer)
        f.grid(row=1, column=0, sticky="ew", pady=(4, 12))
        self.lang_var = tk.StringVar(value=self.ds.label)
        self.lang_cb = ttk.Combobox(f, textvariable=self.lang_var, state="readonly", width=20,
                                    values=[d.label for d in h.DATASETS.values()])
        self.lang_cb.pack(side="left")
        self.lang_cb.bind("<<ComboboxSelected>>", self._on_language)
        ttk.Label(f, text="Translate to", style="Muted.TLabel").pack(side="left", padx=(16, 6))
        self.target_var = tk.StringVar()
        self.target_cb = ttk.Combobox(f, textvariable=self.target_var, state="readonly", width=20)
        self.target_cb.pack(side="left")
        ttk.Label(f, text="via", style="Muted.TLabel").pack(side="left", padx=(16, 6))
        prov = s.get("provider")
        if prov not in h.PROVIDER_CHOICES:
            prov = self.app.provider_var.get()
        self.provider_var = tk.StringVar(value=prov)
        ttk.Combobox(f, textvariable=self.provider_var, values=h.PROVIDER_CHOICES, state="readonly",
                     width=14).pack(side="left")

        # --- what to cache
        ttk.Label(outer, text="WHAT TO CACHE", style="Section.TLabel").grid(row=2, column=0, sticky="w")
        f = ttk.Frame(outer)
        f.grid(row=3, column=0, sticky="ew", pady=(4, 4))
        self.do_defs = tk.BooleanVar(value=bool(s.get("do_defs", True)))
        self.do_trans = tk.BooleanVar(value=bool(s.get("do_trans", True)))
        self.do_tts = tk.BooleanVar(value=bool(s.get("do_tts", False)))
        ttk.Checkbutton(f, text="Definitions", variable=self.do_defs).pack(side="left")
        ttk.Checkbutton(f, text="Translations", variable=self.do_trans).pack(side="left", padx=(16, 0))
        ttk.Button(f, text="⬇  Offline packs", command=self._open_packs).pack(side="left", padx=(8, 0))
        ttk.Checkbutton(f, text="Speech", variable=self.do_tts).pack(side="left", padx=(16, 6))
        scope = s.get("scope")
        self.scope_var = tk.StringVar(value=scope if scope in TTS_SCOPES else TTS_SCOPES[0])
        ttk.Combobox(f, textvariable=self.scope_var, values=list(TTS_SCOPES), state="readonly",
                     width=18).pack(side="left")

        f = ttk.Frame(outer)
        f.grid(row=4, column=0, sticky="ew", pady=(4, 4))
        self.start_var = tk.StringVar(value=str(s.get("start", "1")))
        self.end_var = tk.StringVar(value=str(s.get("end", "")))
        self.flagged_var = tk.BooleanVar(value=bool(s.get("flagged_only", False)))
        self.retry_var = tk.BooleanVar(value=bool(s.get("retry_404", False)))
        ttk.Label(f, text="Rank from", style="Muted.TLabel").pack(side="left")
        ttk.Entry(f, textvariable=self.start_var, width=8).pack(side="left", padx=(6, 8))
        ttk.Label(f, text="to", style="Muted.TLabel").pack(side="left")
        ttk.Entry(f, textvariable=self.end_var, width=8).pack(side="left", padx=(6, 16))
        ttk.Checkbutton(f, text="Only flagged words", variable=self.flagged_var).pack(side="left")
        ttk.Checkbutton(f, text="Retry “not found”", variable=self.retry_var).pack(side="left", padx=(16, 0))

        f = ttk.Frame(outer)
        f.grid(row=5, column=0, sticky="ew", pady=(4, 12))
        self.rate_var = tk.StringVar(value=str(s.get("rate", "950")))
        self.trdelay_var = tk.StringVar(value=str(s.get("tr_delay", "0.3")))
        self.ttsdelay_var = tk.StringVar(value=str(s.get("tts_delay", "0.8")))
        ttk.Label(f, text="Definitions / hour", style="Muted.TLabel").pack(side="left")
        ttk.Entry(f, textvariable=self.rate_var, width=6).pack(side="left", padx=(6, 16))
        ttk.Label(f, text="Pause: translation", style="Muted.TLabel").pack(side="left")
        ttk.Entry(f, textvariable=self.trdelay_var, width=5).pack(side="left", padx=(6, 4))
        ttk.Label(f, text="s   speech", style="Muted.TLabel").pack(side="left")
        ttk.Entry(f, textvariable=self.ttsdelay_var, width=5).pack(side="left", padx=(6, 4))
        ttk.Label(f, text="s", style="Muted.TLabel").pack(side="left")

        # --- cache status
        hdr = ttk.Frame(outer)
        hdr.grid(row=6, column=0, sticky="ew")
        hdr.columnconfigure(0, weight=1)
        ttk.Label(hdr, text="CACHE STATUS", style="Section.TLabel").grid(row=0, column=0, sticky="w")
        self.auto_var = tk.BooleanVar(value=bool(s.get("auto", True)))
        ttk.Checkbutton(hdr, text="Auto cache check", variable=self.auto_var,
                        command=lambda: self.auto_var.get() and self._schedule_scan(100)).grid(
            row=0, column=1, padx=(0, 8))
        ttk.Button(hdr, text="Check now", command=self.check_now).grid(row=0, column=2)

        st = ttk.Frame(outer)
        st.grid(row=7, column=0, sticky="ew", pady=(2, 0))
        st.columnconfigure(1, weight=1)
        for i, (key, title) in enumerate((("defs", "Definitions"), ("tr", "Translations"), ("tts", "Speech"))):
            ttk.Label(st, text=title, width=13).grid(row=i * 2, column=0, sticky="w", pady=(8, 0))
            bar = ttk.Progressbar(st, style="Cache.Horizontal.TProgressbar", mode="determinate",
                                  maximum=1, value=0)
            bar.grid(row=i * 2, column=1, sticky="ew", padx=8, pady=(8, 0))
            val, det = tk.StringVar(value="—"), tk.StringVar()
            ttk.Label(st, textvariable=val, width=20, anchor="e").grid(row=i * 2, column=2, sticky="e",
                                                                       pady=(8, 0))
            ttk.Label(st, textvariable=det, style="Muted.TLabel").grid(row=i * 2 + 1, column=1, columnspan=2,
                                                                       sticky="w", padx=8)
            self._bars[key] = (bar, val, det)
        self.scan_var = tk.StringVar(value="")
        ttk.Label(outer, textvariable=self.scan_var, style="Muted.TLabel").grid(
            row=8, column=0, sticky="w", pady=(8, 8))

        # --- log
        lf = ttk.Frame(outer)
        lf.grid(row=9, column=0, sticky="nsew")
        lf.rowconfigure(0, weight=1)
        lf.columnconfigure(0, weight=1)
        self.log_text = tk.Text(lf, height=8, wrap="word", bg=C["input"], fg=C["text"], bd=0,
                                highlightthickness=0, padx=10, pady=8, font=("Consolas", 9),
                                selectbackground=C["sel"], state="disabled")
        sb = ttk.Scrollbar(lf, orient="vertical", command=self.log_text.yview)
        self.log_text.configure(yscrollcommand=sb.set)
        self.log_text.grid(row=0, column=0, sticky="nsew")
        sb.grid(row=0, column=1, sticky="ns")

        # --- run controls
        f = ttk.Frame(outer)
        f.grid(row=10, column=0, sticky="ew", pady=(12, 0))
        f.columnconfigure(2, weight=1)
        self.start_btn = ttk.Button(f, text="▶  Start crawl", style="Accent.TButton", command=self.start)
        self.start_btn.grid(row=0, column=0)
        self.stop_btn = ttk.Button(f, text="■  Stop", command=self.stop)
        self.stop_btn.grid(row=0, column=1, padx=(8, 12))
        self.stop_btn.state(["disabled"])
        self.run_bar = ttk.Progressbar(f, style="Cache.Horizontal.TProgressbar", mode="determinate",
                                       maximum=1, value=0)
        self.run_bar.grid(row=0, column=2, sticky="ew")
        ttk.Button(f, text="Close", command=self.close).grid(row=0, column=3, padx=(12, 0))
        self.run_var = tk.StringVar(value="Idle")
        ttk.Label(outer, textvariable=self.run_var, style="Muted.TLabel").grid(
            row=11, column=0, sticky="w", pady=(6, 0))
        ttk.Label(outer, style="Muted.TLabel", wraplength=740, justify="left", text=(
            "Speech is saved as Google voice audio (data/lang/tts) and is used by the “Google (online)” voice, "
            "or by “Auto” when no system voice exists. Translations are cached per target language."
        )).grid(row=12, column=0, sticky="w", pady=(6, 0))

        for v in (self.target_var, self.scope_var, self.start_var, self.end_var, self.flagged_var):
            v.trace_add("write", lambda *_: self._schedule_scan())

        for v in (self.do_defs, self.do_trans, self.do_tts, self.scope_var, self.start_var,
                  self.end_var, self.flagged_var, self.retry_var, self.rate_var, self.trdelay_var,
                  self.ttsdelay_var, self.provider_var, self.target_var, self.auto_var):
            v.trace_add("write", self._save)

    # ------------------------------------------------------------------ language
    def _on_language(self, _event=None):
        label = self.lang_var.get()
        code = next((c for c, d in self.h.DATASETS.items() if d.label == label), self.code)
        self.lang_cb.selection_clear()
        self._set_language(code)

    def _set_language(self, code: str):
        h, app = self.h, self.app
        self.code, self.ds = code, h.DATASETS[code]
        self.lang_var.set(self.ds.label)
        self.targets = h.targets_for(self.ds.lang)
        self.target_by_label = dict(self.targets)
        self.target_cb.configure(values=[t[0] for t in self.targets])

        saved_t = self.saved.get("targets", {}).get(code)
        if saved_t in self.target_by_label:
            cur = saved_t
        else:
            cur = app.target_var.get() if code == app.code else ""
        self.target_var.set(cur if cur in self.target_by_label else h.default_target(self.ds.lang))

        self.entries, self.store = [], None
        path = h.wordlist_path(code)
        if path.exists():
            try:
                self.entries = h.load_wordlist(path)
                self.store = app._open_dataset(code)[0]
            except Exception as e:
                self._log(f"Could not read {path}: {e}")
        else:
            self._log(f"Word list not found: {path}")
        self._reset_bars()
        self.scan_var.set(f"{len(self.entries):,} words in {path.name}" if self.entries
                          else "No word list for this language — nothing to crawl.")
        self._schedule_scan(100)

    def _open_packs(self):
        """Offline translation packs for the language / target chosen in this window."""
        self.app._open_offline(self.code, self.target_var.get(), parent=self.win)

    # ------------------------------------------------------------------ options
    def _options(self) -> Options:
        def whole(var, what, default, minimum):
            s = re.sub(r"[\s,_]", "", var.get())
            if not s:
                return default
            try:
                v = int(s)
            except ValueError:
                raise ValueError(f"{what} must be a whole number.")
            if v < minimum:
                raise ValueError(f"{what} must be at least {minimum}.")
            return v

        def seconds(var, what):
            try:
                v = float(var.get().replace(",", ".").strip() or 0)
            except ValueError:
                raise ValueError(f"{what} must be a number of seconds.")
            if v < 0:
                raise ValueError(f"{what} cannot be negative.")
            return v

        start, end = whole(self.start_var, "First rank", 1, 1), whole(self.end_var, "Last rank", None, 1)
        if end is not None and end < start:
            raise ValueError("Last rank must not be smaller than the first rank.")
        rate = whole(self.rate_var, "Definitions per hour", 950, 1)
        if rate > 1000:
            raise ValueError("The API allows at most 1,000 requests per hour.")
        return Options(
            code=self.code, tl=self.target_by_label.get(self.target_var.get(), "en"),
            do_defs=self.do_defs.get(), do_trans=self.do_trans.get(), do_tts=self.do_tts.get(),
            tts_scope=TTS_SCOPES.index(self.scope_var.get()), start=start, end=end,
            flagged_only=self.flagged_var.get(), retry_404=self.retry_var.get(), defs_per_hour=rate,
            tr_delay=seconds(self.trdelay_var, "The translation pause"),
            tts_delay=seconds(self.ttsdelay_var, "The speech pause"),
            provider=self.provider_var.get())

    def _save(self, *_):
        """Persist the window's settings so they survive closing / reopening it."""
        if self._loading or not self.alive():
            return
        targets = self.saved.setdefault("targets", {})
        if self.target_var.get():
            targets[self.code] = self.target_var.get()
        self.saved.update(
            do_defs=self.do_defs.get(), do_trans=self.do_trans.get(), do_tts=self.do_tts.get(),
            scope=self.scope_var.get(), start=self.start_var.get(), end=self.end_var.get(),
            flagged_only=self.flagged_var.get(), retry_404=self.retry_var.get(),
            rate=self.rate_var.get(), tr_delay=self.trdelay_var.get(),
            tts_delay=self.ttsdelay_var.get(), provider=self.provider_var.get(),
            auto=self.auto_var.get(), geometry=self.win.geometry())
        self.h.save_offline_settings(self.saved)

    def _on_configure(self, e):
        if e.widget is not self.win or self._loading:
            return
        if self._geo_job:
            self.win.after_cancel(self._geo_job)
        self._geo_job = self.win.after(600, self._save)

    def _words(self, o: Options):
        flags = self.store.load_flags() if (self.store and o.flagged_only) else set()
        return select_words(self.entries, flags, o)

    # ------------------------------------------------------------------ cache check
    def _schedule_scan(self, delay: int = 800):
        if not self.auto_var.get() or self._running():
            return
        if self._scan_after:
            self.win.after_cancel(self._scan_after)
        self._scan_after = self.win.after(delay, self.check_now)

    def _cancel_scan(self):
        self._scan_stop.set()
        self._scan_token += 1
        if self._scan_after:
            self.win.after_cancel(self._scan_after)
            self._scan_after = None

    def check_now(self):
        self._scan_after = None
        self._cancel_scan()
        if self.store is None or not self.entries:
            return
        try:
            o = self._options()
        except ValueError as e:
            self.scan_var.set(f"Cache check waiting: {e}")
            return
        words = self._words(o)
        self._scan_stop = stop = threading.Event()
        token = self._scan_token
        h, store, ds = self.h, self.store, self.ds
        self.scan_var.set(f"Checking the cache for {len(words):,} words …")

        def work():
            try:
                res = scan_cache(h, store, ds, words, o.tl, o.tts_scope, stop,
                                 lambda i, n: self._emit("scan_progress", token, i, n))
            except Exception as e:
                res = {"error": f"{type(e).__name__}: {e}"}
            self._emit("scan", token, res)

        threading.Thread(target=work, daemon=True).start()

    def _reset_bars(self):
        for bar, val, det in self._bars.values():
            bar.configure(maximum=1, value=0)
            val.set("—")
            det.set("")

    def _show_scan(self, r: dict):
        total = r["total"]
        mx = max(total, 1)
        ok, nf, miss, bad = r["defs_ok"], r["defs_404"], r["defs_missing"], r["defs_corrupt"]
        bar, val, det = self._bars["defs"]
        bar.configure(maximum=mx, value=ok + nf)
        val.set(f"{ok + nf:,} / {total:,}")
        det.set(f"{ok:,} with entry · {nf:,} not found · {miss:,} missing"
                + (f" · {bad:,} damaged (re-fetched on the next crawl)" if bad else ""))

        bar, val, det = self._bars["tr"]
        bar.configure(maximum=mx, value=r["tr_complete"])
        val.set(f"{r['tr_complete']:,} / {total:,}")
        det.set(f"→ {self.target_var.get()} · {r['tr_partial']:,} partial · {r['tr_none']:,} not translated")

        bar, val, det = self._bars["tts"]
        bar.configure(maximum=mx, value=r["tts_words"])
        val.set(f"{r['tts_words']:,} / {total:,}")
        extra = (f" · other texts {r['tts_extra_have']:,} / {r['tts_extra_total']:,}"
                 if r["tts_extra_total"] else "")
        det.set(f"headwords{extra} · {fmt_bytes(r['tts_bytes'])}")
        self.scan_var.set(f"Checked {total:,} words at {time.strftime('%H:%M:%S')}.")

    # ------------------------------------------------------------------ crawl control
    def _running(self) -> bool:
        return self.crawler is not None and self.crawler.is_alive()

    def _set_running(self, running: bool):
        self.start_btn.state(["disabled"] if running else ["!disabled"])
        self.stop_btn.state(["!disabled"] if running else ["disabled"])
        self.lang_cb.configure(state="disabled" if running else "readonly")

    def start(self):
        if self._running():
            return
        if self.store is None or not self.entries:
            messagebox.showinfo("Offline mode", "There is no word list for this language.", parent=self.win)
            return
        try:
            o = self._options()
        except ValueError as e:
            messagebox.showerror("Offline mode", str(e), parent=self.win)
            return
        if not (o.do_defs or o.do_trans or o.do_tts):
            messagebox.showinfo("Offline mode", "Tick at least one of Definitions, Translations or Speech.",
                                parent=self.win)
            return
        words = self._words(o)
        if not words:
            messagebox.showinfo("Offline mode", "No words match the chosen range / flag filter.",
                                parent=self.win)
            return
        self._cancel_scan()
        stores = list({id(s): s for s, _ in self.app._stores.values()}.values())
        self.crawler = Crawler(self.h, self.store, self.ds, words, o, self._emit, stores)
        self.run_bar.configure(maximum=len(words), value=0)
        self.run_var.set("Starting …")
        self._set_running(True)
        self.crawler.start()

    def stop(self):
        if self._running():
            self.crawler.stop_event.set()
            self.run_var.set("Stopping … (finishing the current request)")

    def close(self):
        if self._running():
            if not messagebox.askyesno("Offline mode", "A crawl is running. Stop it and close this window?",
                                       parent=self.win):
                return
            self.crawler.stop_event.set()
        self._save()
        self._cancel_scan()
        self.win.destroy()

    # ------------------------------------------------------------------ events (UI thread)
    def _emit(self, *event):
        """Called from worker threads: hand the event to the app's queue (see App._poll_queue)."""
        self.app.q.put(("call", self._on_event) + event)

    def _on_event(self, kind: str, *a):
        if not self.alive():
            return
        if kind == "log":
            self._log(a[0])
        elif kind == "progress":
            n, total, rank, word, st = a
            self.run_bar.configure(maximum=max(total, 1), value=n)
            self.run_var.set(
                f"{n:,} / {total:,} · #{rank:,} “{word}” · {st['defs']:,} definitions, {st['nf']:,} not found, "
                f"{st['tr']:,} translated, {st['tts']:,} audio, {st['errors']:,} errors")
        elif kind == "done":
            st, elapsed, stopped = a
            self._set_running(False)
            msg = (f"{'Stopped' if stopped else 'Finished'} after {fmt_dur(elapsed)}: {st['words']:,} words · "
                   f"{st['defs']:,} definitions · {st['nf']:,} not found · {st['fixed']:,} repaired · "
                   f"{st['tr']:,} translated · {st['tts']:,} audio · {st['errors']:,} errors")
            self.run_var.set(msg)
            self._log(msg)
            self._schedule_scan(300)
            if self.code == self.app.code:
                self.app._scan_definitions()
        elif kind == "scan_progress":
            token, i, n = a
            if token == self._scan_token:
                self.scan_var.set(f"Checking the cache … {i:,} / {n:,}")
        elif kind == "scan":
            token, res = a
            if token != self._scan_token or res is None:
                return
            if "error" in res:
                self.scan_var.set(f"Cache check failed: {res['error']}")
            else:
                self._show_scan(res)

    def _log(self, msg: str):
        t = self.log_text
        t.configure(state="normal")
        t.insert("end", f"[{time.strftime('%H:%M:%S')}] {msg}\n")
        if int(t.index("end-1c").split(".")[0]) > 500:
            t.delete("1.0", "101.0")
        t.see("end")
        t.configure(state="disabled")


def open_offline_mode(app, host):
    """Open (or raise) the offline-mode window. `host` is the corpus module."""
    win = getattr(app, "_ofm", None)
    if win is not None and win.alive():
        win.win.lift()
        win.win.focus_set()
        return
    app._ofm = OfflineWindow(app, host)
