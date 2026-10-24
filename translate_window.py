"""
Text translator for Corpus
==========================

A window (opened with the "Translate text" button next to "Offline mode" and "Coverage") where you
type or paste a whole text and translate it into any language the app knows.

* The text is split into lines, and every line into sentence-sized pieces, so paragraphs survive
  and long texts fit the limits of every translation provider.
* It uses its own Translator (own provider cool-downs) with the same providers and fail-over as the
  rest of the app; the provider is chosen in the window ("Auto" = fail-over).
* Free text is never written to the dictionary database: the cache is replaced by NullStore.

Everything that belongs to the main script (Translator, language names, palette ...) is reached
through the `host` module that corpus.py passes in, so this file never imports corpus.py.
"""
from __future__ import annotations

import re
import threading
import tkinter as tk
from tkinter import ttk

AUTO = "Auto-detect"
NO_SPACE = {"zh-CN", "ja"}                 # pieces are glued without a space in these languages
PIECE_LIMIT = {"MyMemory": 150, "Lingva": 300}   # characters per request piece, by provider
DEFAULT_LIMIT = 400
BATCH = 20                                  # unique pieces per call (progress / stop granularity)
SPEAK_MAX = 2000                            # longest text sent to the speech engine
SENT_SPLIT = re.compile(r"(?<=[.!?…])\s+|(?<=[。！？])")
CJK_END = re.compile(r"[\u3000-\u9fff\uff00-\uffef]$")


# --------------------------------------------------------------------------- text <-> pieces
def _glue(a: str, b: str) -> str:
    if not a:
        return b
    return a + ("" if CJK_END.search(a) else " ") + b


def split_line(line: str, limit: int) -> list[str]:
    """One line -> pieces of at most `limit` characters, cut at sentence ends where possible."""
    pieces: list[str] = []
    cur = ""
    for s in SENT_SPLIT.split(line):
        s = " ".join(s.split())
        if not s:
            continue
        while len(s) > limit:                       # a single huge sentence: cut at a space
            cut = s.rfind(" ", 0, limit)
            if cut <= 0:
                cut = limit
            if cur:
                pieces.append(cur)
                cur = ""
            pieces.append(s[:cut].strip())
            s = s[cut:].strip()
        if cur and len(cur) + 1 + len(s) > limit:
            pieces.append(cur)
            cur = s
        else:
            cur = _glue(cur, s)
    if cur:
        pieces.append(cur)
    return pieces


def parse(text: str, limit: int):
    """-> (structure, pieces). structure = [(indent, [piece, ...]), ...], one entry per line;
    a blank line is ("", [])."""
    structure: list[tuple[str, list[str]]] = []
    pieces: list[str] = []
    for raw in text.splitlines():
        stripped = raw.strip()
        if not stripped:
            structure.append(("", []))
            continue
        indent = raw[: len(raw) - len(raw.lstrip())]
        ps = split_line(stripped, limit)
        structure.append((indent, ps))
        pieces += ps
    return structure, pieces


def assemble(structure, done: dict[str, str], tl: str) -> str:
    sep = "" if tl in NO_SPACE else " "
    lines = []
    for indent, ps in structure:
        lines.append(indent + sep.join(done[p].strip() for p in ps) if ps else "")
    return "\n".join(lines)


class NullStore:
    """Translator cache that keeps nothing: free text is always translated afresh."""

    def get_translation(self, key: str, tl: str):
        return None

    def put_translation(self, key: str, tl: str, text: str):
        pass


# --------------------------------------------------------------------------- the window
class TranslateWindow:
    def __init__(self, app, host):
        self.app, self.h = app, host
        C = host.C
        self.translator = host.Translator(NullStore())
        self._token = 0
        self._cancel = threading.Event()
        self._running = False

        langs = sorted(host.targets_for(""), key=lambda t: t[0].lower())   # every language, A-Z
        self.src_map = {AUTO: "auto", **dict(langs)}
        self.tgt_map = dict(langs)

        ui = app.ui
        src = ui.get("tx_source")
        src = src if src in self.src_map else AUTO
        tgt = ui.get("tx_target")
        if tgt not in self.tgt_map:
            tgt = app.target_var.get()
        if tgt not in self.tgt_map:
            tgt = host.default_target(app.lang)
        prov = ui.get("tx_provider")
        prov = prov if prov in host.PROVIDER_CHOICES else app.provider_var.get()

        self.win = win = tk.Toplevel(app)
        win.title("Text translator")
        win.configure(bg=C["bg"])
        win.geometry(host.fit_geometry(win, ui.get("tx_geometry"), "900x720"))
        app._remember_geometry(win, "tx_geometry")
        win.minsize(700, 520)
        win.transient(app)
        win.protocol("WM_DELETE_WINDOW", self.close)

        self.src_var = tk.StringVar(value=src)
        self.tgt_var = tk.StringVar(value=tgt)
        self.prov_var = tk.StringVar(value=prov)
        self._out_lang = self.tgt_map[tgt]
        self._build()

        saved = getattr(app, "_tx_saved", None)         # text of the previous visit this session
        if saved:
            self.inp.insert("1.0", saved[0])
            self._set_output(saved[1])
        for key, var in (("tx_source", self.src_var), ("tx_target", self.tgt_var),
                         ("tx_provider", self.prov_var)):
            var.trace_add("write", lambda *_, k=key, v=var: self.app._ui_set(k, v.get()))
        self.inp.focus_set()

    def alive(self) -> bool:
        return bool(self.win.winfo_exists())

    # ------------------------------------------------------------------ layout
    def _text_box(self, parent, editable: bool):
        C = self.h.C
        frame = ttk.Frame(parent)
        frame.rowconfigure(0, weight=1)
        frame.columnconfigure(0, weight=1)
        t = tk.Text(frame, wrap="word", bg=C["input"], fg=C["text"], bd=0, highlightthickness=0,
                    padx=12, pady=10, insertbackground=C["text"], selectbackground=C["sel"],
                    selectforeground="#ffffff", font=("Segoe UI", 12), spacing1=2, spacing3=2,
                    undo=editable, exportselection=False)
        sb = ttk.Scrollbar(frame, orient="vertical", command=t.yview)
        t.configure(yscrollcommand=sb.set)
        t.grid(row=0, column=0, sticky="nsew")
        sb.grid(row=0, column=1, sticky="ns")
        t.bind("<Control-a>", self._select_all)
        t.bind("<Shift-Return>", self._line_break)
        return frame, t

    @staticmethod
    def _select_all(e):
        e.widget.tag_add("sel", "1.0", "end-1c")
        return "break"

    def _line_break(e):
        e.widget.insert("insert", "\n")
        return "break"

    def _build(self):
        C = self.h.C
        win = self.win
        ttk.Style(win).configure("Tx.Horizontal.TProgressbar", troughcolor=C["input"],
                                 background=C["accent"], bordercolor=C["border"],
                                 lightcolor=C["accent"], darkcolor=C["accent"], thickness=14)

        outer = ttk.Frame(win, padding=16)
        outer.pack(fill="both", expand=True, padx=10, pady=10)
        outer.columnconfigure(0, weight=1)
        outer.rowconfigure(2, weight=1)

        ttk.Label(outer, text="TEXT TRANSLATOR", style="Section.TLabel").grid(row=0, column=0, sticky="w")

        # --- languages
        f = ttk.Frame(outer)
        f.grid(row=1, column=0, sticky="ew", pady=(4, 12))
        ttk.Label(f, text="From", style="Muted.TLabel").pack(side="left")
        ttk.Combobox(f, textvariable=self.src_var, values=list(self.src_map), state="readonly",
                     width=19).pack(side="left", padx=(6, 6))
        self.swap_btn = ttk.Button(f, text="⇄", width=3, command=self.swap)
        self.swap_btn.pack(side="left")
        ttk.Label(f, text="To", style="Muted.TLabel").pack(side="left", padx=(12, 6))
        ttk.Combobox(f, textvariable=self.tgt_var, values=list(self.tgt_map), state="readonly",
                     width=19).pack(side="left")
        ttk.Label(f, text="via", style="Muted.TLabel").pack(side="left", padx=(16, 6))
        ttk.Combobox(f, textvariable=self.prov_var, values=self.h.PROVIDER_CHOICES, state="readonly",
                     width=14).pack(side="left")

        # --- original + translation, resizable
        pw = tk.PanedWindow(outer, orient="vertical", bg=C["bg"], sashwidth=8, bd=0, sashrelief="flat")
        pw.grid(row=2, column=0, sticky="nsew")

        top = ttk.Frame(pw)
        top.columnconfigure(0, weight=1)
        top.rowconfigure(1, weight=1)
        hdr = ttk.Frame(top)
        hdr.grid(row=0, column=0, sticky="ew", pady=(0, 4))
        hdr.columnconfigure(1, weight=1)
        ttk.Label(hdr, text="ORIGINAL", style="Section.TLabel").grid(row=0, column=0, sticky="w")
        self.count_var = tk.StringVar(value="0 characters")
        ttk.Label(hdr, textvariable=self.count_var, style="Muted.TLabel").grid(row=0, column=1, sticky="e", padx=(0, 10))
        ttk.Button(hdr, text="🔊", width=3, command=self.speak_input).grid(row=0, column=2)
        frame, self.inp = self._text_box(top, True)
        frame.grid(row=1, column=0, sticky="nsew")
        self.inp.bind("<<Modified>>", self._on_modified)
        self.inp.bind("<Return>", lambda e: (self.translate(), "break")[1])

        bottom = ttk.Frame(pw)
        bottom.columnconfigure(0, weight=1)
        bottom.rowconfigure(1, weight=1)
        hdr = ttk.Frame(bottom)
        hdr.grid(row=0, column=0, sticky="ew", pady=(8, 4))
        hdr.columnconfigure(0, weight=1)
        ttk.Label(hdr, text="TRANSLATION", style="Section.TLabel").grid(row=0, column=0, sticky="w")
        ttk.Button(hdr, text="📋  Copy", command=self.copy).grid(row=0, column=1, padx=(0, 6))
        ttk.Button(hdr, text="🔊", width=3, command=self.speak_output).grid(row=0, column=2)
        frame, self.out = self._text_box(bottom, False)
        frame.grid(row=1, column=0, sticky="nsew")
        self.out.bind("<Button-1>", lambda e: self.out.focus_set())
        self.out.configure(state="disabled")

        pw.add(top, minsize=150, stretch="always")
        pw.add(bottom, minsize=150, stretch="always")

        # --- run controls
        f = ttk.Frame(outer)
        f.grid(row=3, column=0, sticky="ew", pady=(12, 0))
        f.columnconfigure(3, weight=1)
        self.go_btn = ttk.Button(f, text="🌐  Translate", style="Accent.TButton", command=self.translate)
        self.go_btn.grid(row=0, column=0)
        self.stop_btn = ttk.Button(f, text="■  Stop", command=self.stop)
        self.stop_btn.grid(row=0, column=1, padx=(8, 8))
        self.stop_btn.state(["disabled"])
        self.clear_btn = ttk.Button(f, text="Clear", command=self.clear)
        self.clear_btn.grid(row=0, column=2)
        self.bar = ttk.Progressbar(f, style="Tx.Horizontal.TProgressbar", mode="determinate",
                                   maximum=1, value=0)
        self.bar.grid(row=0, column=3, sticky="ew", padx=(12, 12))
        ttk.Button(f, text="Close", command=self.close).grid(row=0, column=4)

        self.status_var = tk.StringVar(value="Type or paste a text and press Translate (Enter).")
        ttk.Label(outer, textvariable=self.status_var, style="Muted.TLabel", wraplength=820,
                  justify="left").grid(row=4, column=0, sticky="w", pady=(8, 0))

    # ------------------------------------------------------------------ small actions
    def _on_modified(self, _e=None):
        if self.inp.edit_modified():
            n = len(self.inp.get("1.0", "end-1c"))
            self.count_var.set(f"{n:,} characters")
            self.inp.edit_modified(False)

    def _set_output(self, text: str):
        t = self.out
        t.configure(state="normal")
        t.delete("1.0", "end")
        t.insert("1.0", text)
        t.configure(state="disabled")

    def _set_running(self, running: bool):
        self._running = running
        self.go_btn.state(["disabled"] if running else ["!disabled"])
        self.stop_btn.state(["!disabled"] if running else ["disabled"])
        self.clear_btn.state(["disabled"] if running else ["!disabled"])
        self.swap_btn.state(["disabled"] if running else ["!disabled"])

    def clear(self):
        if self._running:
            return
        self.inp.delete("1.0", "end")
        self._set_output("")
        self.bar.configure(maximum=1, value=0)
        self.status_var.set("Cleared.")
        self.inp.focus_set()

    def swap(self):
        if self._running:
            return
        if self.src_map[self.src_var.get()] == "auto":
            self.status_var.set("Choose a source language first — Auto-detect cannot be swapped.")
            return
        old_src, old_tgt = self.src_var.get(), self.tgt_var.get()
        self.src_var.set(old_tgt)
        self.tgt_var.set(old_src)
        out = self.out.get("1.0", "end-1c")
        if out.strip():                                   # the translation becomes the new original
            self.inp.delete("1.0", "end")
            self.inp.insert("1.0", out)
            self._set_output("")

    def copy(self):
        text = self.out.get("1.0", "end-1c")
        if text:
            self.win.clipboard_clear()
            self.win.clipboard_append(text)
            self.status_var.set("Translation copied to the clipboard.")

    # ------------------------------------------------------------------ speech (selection, or all)
    def _speak(self, widget: tk.Text, lang: str):
        try:
            text = widget.get("sel.first", "sel.last")
        except tk.TclError:
            text = widget.get("1.0", "end-1c")
        text = text.strip()
        if not text:
            return
        if len(text) > SPEAK_MAX:
            text = text[:SPEAK_MAX]
            self.status_var.set(f"Speaking the first {SPEAK_MAX:,} characters (select a passage to hear another part).")
        self.app._speak(text, lang)

    def speak_input(self):
        sl = self.src_map[self.src_var.get()]
        if sl == "auto":
            self.status_var.set("Choose a source language to hear the original.")
            return
        self._speak(self.inp, sl)

    def speak_output(self):
        self._speak(self.out, self._out_lang)

    # ------------------------------------------------------------------ translate
    def translate(self):
        if self._running:
            return
        text = self.inp.get("1.0", "end-1c")
        if not text.strip():
            self.status_var.set("Type or paste some text first.")
            return
        sl = self.src_map[self.src_var.get()]
        tl = self.tgt_map[self.tgt_var.get()]
        provider = self.prov_var.get()
        note = ""
        if sl == "auto" and provider == "Offline":
            sl = self.app.lang                            # Argos cannot detect the language
            note = (f"  (Offline cannot detect the language; assuming "
                    f"{self.h.LANG_NAMES.get(sl, sl)} — pick a source language to change that)")

        structure, pieces = parse(text, PIECE_LIMIT.get(provider, DEFAULT_LIMIT))
        uniq = list(dict.fromkeys(pieces))
        self._token += 1
        self._cancel = cancel = threading.Event()
        self._set_running(True)
        self.bar.configure(maximum=max(len(uniq), 1), value=0)
        self.status_var.set(f"Translating {len(uniq):,} segment(s) via {provider} …{note}")
        threading.Thread(target=self._worker, daemon=True,
                         args=(self._token, cancel, structure, uniq, sl, tl, provider, note)).start()

    def stop(self):
        if self._running:
            self._cancel.set()
            self.status_var.set("Stopping … (finishing the current batch)")

    def _worker(self, token, cancel, structure, uniq, sl, tl, provider, note):
        try:
            tr = self.translator
            tr.mode = provider
            done: dict[str, str] = {}
            for i in range(0, len(uniq), BATCH):
                if cancel.is_set():
                    self._emit("stopped", token)
                    return
                batch = uniq[i:i + BATCH]
                done.update(zip(batch, tr.many(batch, tl, sl)))
                self._emit("progress", token, len(done), len(uniq))
            self._emit("result", token, assemble(structure, done, tl), tl, tr.last_provider, note)
        except Exception as e:
            self._emit("error", token, str(e))

    # ------------------------------------------------------------------ events (UI thread)
    def _emit(self, *event):
        """Called from the worker thread: hand the event to the app's queue (see App._poll_queue)."""
        self.app.q.put(("call", self._on_event) + event)

    def _on_event(self, kind: str, token: int, *a):
        if not self.alive() or token != self._token:
            return
        if kind == "progress":
            n, total = a
            self.bar.configure(value=n)
            self.status_var.set(f"Translating … {n:,} / {total:,} segments")
        elif kind == "result":
            text, tl, used, note = a
            self._out_lang = tl
            self._set_output(text)
            self.bar.configure(value=self.bar.cget("maximum"))
            self.status_var.set(f"Done via {used}: {len(text):,} characters.{note}")
            self._set_running(False)
        elif kind == "stopped":
            self.status_var.set("Stopped.")
            self._set_running(False)
        elif kind == "error":
            self.status_var.set(f"Translation failed: {a[0]}")
            self._set_running(False)

    # ------------------------------------------------------------------ closing
    def close(self):
        self._cancel.set()
        self._token += 1                                  # late results of a stopped run are ignored
        self.app._tx_saved = (self.inp.get("1.0", "end-1c"), self.out.get("1.0", "end-1c"))
        self.win.destroy()


def open_translate_window(app, host):
    """Open (or raise) the text-translator window. `host` is the corpus module."""
    win = getattr(app, "_trw", None)
    if win is not None and win.alive():
        win.win.lift()
        win.inp.focus_set()
        return
    app._trw = TranslateWindow(app, host)
