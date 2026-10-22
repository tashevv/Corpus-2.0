#!/usr/bin/env python3

from __future__ import annotations

import sys
import os

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "lib"))

import unicodedata
import bisect
from itertools import accumulate
import hashlib
import importlib.util
import json
import queue
import re
import shutil
import sqlite3
import subprocess
import threading
import time
import tkinter as tk
import urllib.error
import urllib.parse
import urllib.request
from dataclasses import dataclass, replace
from pathlib import Path
from tkinter import filedialog, messagebox, ttk

from offline_mode import open_offline_mode  # noqa: E402
from translate_window import open_translate_window  # noqa: E402
import tempfile

# --------------------------------------------------------------------------- paths
APP_DIR = Path(__file__).resolve().parent
DATA_DIR = APP_DIR / "data/lang"
TTS_DIR = DATA_DIR / "tts"                 # shared: the cache is keyed by language + text
SETTINGS_PATH = DATA_DIR / "settings.json"

DICT_URL = "https://freedictionaryapi.com/api/v1/entries/{lang}/{word}?translations=true"
GT_URL = "https://translate.googleapis.com/translate_a/single"
GTTS_URL = "https://translate.google.com/translate_tts"
USER_AGENT = "Mozilla/5.0 (X11; Linux x86_64) RuFrequencyDictionary/1.0"

TITLE = "Corpus 2.0 — Frequency Dictionary"

# --------------------------------------------------------------------------- data sets
@dataclass(frozen=True)
class Dataset:
    code: str        # folder name under data/lang/ and key in DATASETS
    label: str       # shown in the selector
    lang: str        # language code for speech + translation (Google style)
    wordlist: str
    dict_lang: str   # language code for freedictionaryapi.com (Wiktionary)
    title: str = TITLE
    fallback: str = ""   # used when `wordlist` is missing from the folder

def _ds(code, label, lang=None, dict_lang=None, wordlist=None):
    lang = lang or code
    return Dataset(code, label, lang, wordlist or f"{code}_50k.txt", dict_lang or lang,
                   fallback=f"{code}_full.txt" if wordlist is None else "")

_DATASETS = [
    _ds("af", "Afrikaans"), _ds("ar", "Arabic"), _ds("bg", "Bulgarian"), _ds("bn", "Bengali"),
    _ds("br", "Breton"), _ds("bs", "Bosnian", dict_lang="sh"), _ds("ca", "Catalan"),
    _ds("cs", "Czech"), _ds("da", "Danish"), _ds("de", "German"), _ds("el", "Greek"),
    _ds("en", "English"),
    _ds("en (Legacy)", "English (legacy)", lang="en", wordlist="en_60k.txt"),
    _ds("eo", "Esperanto"), _ds("es", "Spanish"), _ds("et", "Estonian"), _ds("eu", "Basque"),
    _ds("fa", "Persian"), _ds("fi", "Finnish"), _ds("fr", "French"), _ds("gl", "Galician"),
    _ds("he", "Hebrew"), _ds("hi", "Hindi"), _ds("hr", "Croatian", dict_lang="sh"),
    _ds("hu", "Hungarian"), _ds("hy", "Armenian"), _ds("id", "Indonesian"), _ds("is", "Icelandic"),
    _ds("it", "Italian"), _ds("ja", "Japanese"), _ds("ka", "Georgian"), _ds("kk", "Kazakh"),
    _ds("ko", "Korean"), _ds("lt", "Lithuanian"), _ds("lv", "Latvian"), _ds("mk", "Macedonian"),
    _ds("ml", "Malayalam"), _ds("ms", "Malay"), _ds("nl", "Dutch"),
    _ds("no", "Norwegian", dict_lang="nb"), _ds("pl", "Polish"), _ds("pt", "Portuguese"),
    _ds("pt_br", "Portuguese (Brazil)", lang="pt", dict_lang="pt"), _ds("ro", "Romanian"),
    _ds("ru", "Russian"), _ds("si", "Sinhala"), _ds("sk", "Slovak"), _ds("sl", "Slovenian"),
    _ds("sq", "Albanian"), _ds("sr", "Serbian", dict_lang="sh"), _ds("sv", "Swedish"),
    _ds("ta", "Tamil"), _ds("te", "Telugu"), _ds("th", "Thai"), _ds("tl", "Tagalog"),
    _ds("tr", "Turkish"), _ds("uk", "Ukrainian"), _ds("ur", "Urdu"), _ds("vi", "Vietnamese"),
    _ds("ze_en", "English (ze_en)", lang="en"),
    _ds("ze_zh", "Chinese (ze_zh)", lang="zh-CN", dict_lang="zh"),
    _ds("zh_cn", "Chinese (Simplified)", lang="zh-CN", dict_lang="zh"),
    _ds("zh_tw", "Chinese (Traditional)", lang="zh-CN", dict_lang="zh"),
]
DATASETS = {d.code: d for d in sorted(_DATASETS, key=lambda d: d.label.lower())}


def data_dir(code: str) -> Path:
    return DATA_DIR / code


def wordlist_path(code: str) -> Path:
    ds = DATASETS[code]
    primary = data_dir(code) / ds.wordlist
    if not primary.exists() and ds.fallback:
        alt = data_dir(code) / ds.fallback
        if alt.exists():
            return alt
    return primary


def db_path(code: str) -> Path:
    return data_dir(code) / "dictionary.db"

SMALL_BODY = 2000   # a response without entries is a few hundred bytes; real entries are much larger


def scan_definitions(path: Path) -> tuple[set[str], set[str]]:
    """Read a data set's database -> (defined, empty).
    defined = stored with at least one dictionary entry; empty = stored but without any entry
    (HTTP 404, an "entries": [] response, or a damaged body). Words never looked up are in neither.
    Meant to run in a background thread (it opens its own connection)."""
    conn = sqlite3.connect(path, timeout=30)
    try:
        stored = {w for (w,) in conn.execute("SELECT word FROM entries WHERE status=200")}
        empty: set[str] = set()
        for word, status, body in conn.execute(
                "SELECT word, status, body FROM entries WHERE status=404 OR length(body) < ?",
                (SMALL_BODY,)):
            if status == 404:
                empty.add(word)
                continue
            try:
                data = json.loads(body)
            except ValueError:
                empty.add(word)
                continue
            if not (isinstance(data, dict) and data.get("entries")):
                empty.add(word)
    finally:
        conn.close()
    return stored - empty, empty

def _read_settings() -> dict:
    try:
        data = json.loads(SETTINGS_PATH.read_text("utf-8"))
        return data if isinstance(data, dict) else {}
    except Exception:
        return {}


def _write_settings(data: dict):
    try:
        DATA_DIR.mkdir(parents=True, exist_ok=True)
        SETTINGS_PATH.write_text(json.dumps(data, ensure_ascii=False, indent=2), "utf-8")
    except OSError:
        pass


def load_last_dataset() -> str:
    code = _read_settings().get("dataset")
    return code if code in DATASETS else "ru"


def save_last_dataset(code: str):
    data = _read_settings()
    data["dataset"] = code
    _write_settings(data)


def load_offline_settings() -> dict:
    d = _read_settings().get("offline")
    return d if isinstance(d, dict) else {}

def offline_flag(key: str, default: bool = True) -> bool:
    """Current value of a checkbox from the Offline mode window (read from settings.json)."""
    return bool(load_offline_settings().get(key, default))

def save_offline_settings(d: dict):
    data = _read_settings()
    data["offline"] = d
    _write_settings(data)

def load_ui_settings() -> dict:
    d = _read_settings().get("ui")
    return d if isinstance(d, dict) else {}


def save_ui_settings(d: dict):
    data = _read_settings()
    data["ui"] = d
    _write_settings(data)


def fit_geometry(win, geo, default: str) -> str:
    """Saved 'WxH+X+Y' -> a safe geometry string (the position is dropped if it is off-screen)."""
    m = re.fullmatch(r"(\d+)x(\d+)\+(-?\d+)\+(-?\d+)", geo) if isinstance(geo, str) else None
    if not m:
        return default
    w, h, x, y = map(int, m.groups())
    sw, sh = win.winfo_screenwidth(), win.winfo_screenheight()
    w, h = min(w, sw), min(h, sh)
    if x < -20 or y < -20 or x > sw - 100 or y > sh - 100:
        return f"{w}x{h}"
    return f"{w}x{h}+{x}+{y}"

# --------------------------------------------------------------------------- languages
LANG_NAMES = {
    "ru": "Russian", "en": "English", "uk": "Ukrainian", "bg": "Bulgarian", "de": "German",
    "fr": "French", "es": "Spanish", "it": "Italian", "pt": "Portuguese", "pl": "Polish",
    "cs": "Czech", "sk": "Slovak", "sr": "Serbian", "hr": "Croatian", "sl": "Slovenian",
    "ro": "Romanian", "hu": "Hungarian", "el": "Greek", "tr": "Turkish", "nl": "Dutch",
    "sv": "Swedish", "no": "Norwegian", "da": "Danish", "fi": "Finnish", "lv": "Latvian",
    "lt": "Lithuanian", "et": "Estonian", "be": "Belarusian", "ka": "Georgian",
    "hy": "Armenian", "kk": "Kazakh", "he": "Hebrew", "ar": "Arabic", "fa": "Persian",
    "hi": "Hindi", "zh-CN": "Chinese (Simplified)", "ja": "Japanese", "ko": "Korean",
    "vi": "Vietnamese", "th": "Thai", "id": "Indonesian",
    "af": "Afrikaans", "bn": "Bengali", "br": "Breton", "bs": "Bosnian", "ca": "Catalan",
    "eo": "Esperanto", "eu": "Basque", "gl": "Galician", "is": "Icelandic", "mk": "Macedonian",
    "ml": "Malayalam", "ms": "Malay", "si": "Sinhala", "sq": "Albanian", "ta": "Tamil",
    "te": "Telugu", "tl": "Tagalog", "ur": "Urdu",
}


def targets_for(lang: str):
    """Translation targets offered for a data set (everything except its own language)."""
    return [(f"{name} ({code})", code) for code, name in LANG_NAMES.items() if code != lang]


def default_target(lang: str) -> str:
    return "Russian (ru)" if lang == "en" else "English (en)"


# --------------------------------------------------------------------------- palette
C = dict(
    bg="#0d1014", panel="#151922", card="#1a1f29", input="#232a36", border="#2b3342",
    text="#e7eaf0", muted="#8a93a6", accent="#7c9cff", accent_hi="#9ab2ff", sel="#2d3d73",
    hover="#2a3550", gold="#f6c744", danger="#ff6b6b", stripe="#1e2430", green="#9fd6b4",
    red="#e0a0a0", bad="#4a2226", empty="#5a2429",
)
FONT = ("Segoe UI", 10)
FONT_B = ("Segoe UI", 10, "bold")
MONO = ("Consolas", 10)

# --------------------------------------------------------------------------- app icon (PNG, base64)
ICON_256_B64 = """
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
YII=
"""

ICON_32_B64 = """
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
"""

# --------------------------------------------------------------------------- word list
# Cyrillic alphabets that Unicode order gets wrong (ё after е, ґ є і ї, ђ ћ ...).
ALPHABETS = {
    "ru": "абвгдеёжзийклмнопрстуфхцчшщъыьэюя",
    "uk": "абвгґдеєжзиіїйклмнопрстуфхцчшщьюя",
    "bg": "абвгдежзийклмнопрстуфхцчшщъьюя",
    "mk": "абвгдѓежзѕијклљмнњопрстќуфхцчџш",
    "sr": "абвгдђежзијклљмнњопрстћуфхцчџш",
    "kk": "аәбвгғдеёжзийкқлмнңоөпрстуұүфхһцчшщъыіьэюя",
}
_ALPHA_MAPS = {c: {ord(ch): chr(0xE000 + i) for i, ch in enumerate(a)} for c, a in ALPHABETS.items()}
_ACCENTS = re.compile("[\u0300-\u036f]")        # combining diacritics only
KEEP_ACCENTS = {"ru", "uk", "bg", "mk", "kk"}    # й, ї, ѓ ... are real letters here


def _base(s: str) -> str:
    return unicodedata.normalize("NFC", s.lower()).replace("ς", "σ")


def alpha_key(s: str, code: str = "ru") -> str:
    """Sort key: follows the language's alphabet where Unicode order is wrong, ignores accents."""
    s = _base(s)
    m = _ALPHA_MAPS.get(code)
    if m:
        s = s.translate(m)
    return _ACCENTS.sub("", unicodedata.normalize("NFD", s))


def fold(s: str, code: str = "ru") -> str:
    """Case-, ё/е- and (where sensible) accent-insensitive form used for searching."""
    s = _base(s).replace("ё", "е")
    if code not in KEEP_ACCENTS:
        s = unicodedata.normalize("NFC", _ACCENTS.sub("", unicodedata.normalize("NFD", s)))
    return s


@dataclass
class Entry:
    rank: int
    word: str
    freq: int


def load_wordlist(path: Path) -> list[Entry]:
    """Parse 'word frequency' lines (split on a space); rank is the row number."""
    entries: list[Entry] = []
    with open(path, encoding="utf-8-sig") as fh:
        for line in fh:
            line = line.strip()
            if not line:
                continue
            parts = line.rsplit(" ", 1)
            if len(parts) != 2:
                continue
            try:
                freq = int(parts[1])
            except ValueError:
                continue
            entries.append(Entry(len(entries) + 1, parts[0], freq))
    return entries


# --------------------------------------------------------------------------- storage
class Store:
    """SQLite store: API responses, flags, translations (one database per data set)."""

    def __init__(self, path: Path):
        path.parent.mkdir(parents=True, exist_ok=True)
        self.lock = threading.Lock()
        self.conn = sqlite3.connect(path, check_same_thread=False)
        with self.lock, self.conn:
            self.conn.executescript(
                """
                CREATE TABLE IF NOT EXISTS entries (
                    word TEXT PRIMARY KEY, status INTEGER NOT NULL,
                    body TEXT NOT NULL, fetched_at TEXT NOT NULL);
                CREATE TABLE IF NOT EXISTS flags (
                    word TEXT PRIMARY KEY, flagged_at TEXT NOT NULL);
                CREATE TABLE IF NOT EXISTS translations (
                    key TEXT NOT NULL, tl TEXT NOT NULL, text TEXT NOT NULL,
                    PRIMARY KEY (key, tl));
                """
            )

    def get_entry(self, word: str):
        with self.lock:
            return self.conn.execute(
                "SELECT status, body FROM entries WHERE word=?", (word,)
            ).fetchone()

    def put_entry(self, word: str, status: int, body: str):
        with self.lock, self.conn:
            self.conn.execute(
                "INSERT OR REPLACE INTO entries VALUES (?,?,?,datetime('now'))",
                (word, status, body),
            )

    def load_flags(self) -> set[str]:
        with self.lock:
            return {r[0] for r in self.conn.execute("SELECT word FROM flags")}

    def set_flags(self, words: list[str], flagged: bool):
        with self.lock, self.conn:
            if flagged:
                self.conn.executemany(
                    "INSERT OR REPLACE INTO flags VALUES (?, datetime('now'))",
                    [(w,) for w in words],
                )
            else:
                self.conn.executemany("DELETE FROM flags WHERE word=?", [(w,) for w in words])

    def get_translation(self, key: str, tl: str):
        with self.lock:
            row = self.conn.execute(
                "SELECT text FROM translations WHERE key=? AND tl=?", (key, tl)
            ).fetchone()
        return row[0] if row else None

    def put_translation(self, key: str, tl: str, text: str):
        with self.lock, self.conn:
            self.conn.execute("INSERT OR REPLACE INTO translations VALUES (?,?,?)", (key, tl, text))

class GatedStore:
    """Store view used by the interactive Translator: reads always work, but a translation is
    only written to the database when Offline mode → Translations is checked."""

    def __init__(self, store: Store):
        self._s = store

    def __getattr__(self, name):
        return getattr(self._s, name)

    def put_translation(self, key: str, tl: str, text: str):
        if offline_flag("do_trans"):
            self._s.put_translation(key, tl, text)

# --------------------------------------------------------------------------- dictionary API
def fetch_entry(word: str, lang: str = "ru") -> tuple[int, str]:
    """Return (http_status, body). Network errors propagate as URLError/OSError."""
    url = DICT_URL.format(lang=lang, word=urllib.parse.quote(word, safe=""))
    req = urllib.request.Request(
        url, headers={"User-Agent": USER_AGENT, "Accept": "application/json"}
    )
    try:
        with urllib.request.urlopen(req, timeout=20) as resp:
            return resp.status, resp.read().decode("utf-8")
    except urllib.error.HTTPError as e:
        return e.code, e.read().decode("utf-8", "replace")


@dataclass
class Block:
    """One displayable (and clickable) piece of text."""
    kind: str
    text: str
    level: int = 0
    prefix: str = ""
    lang: str = "ru"          # language of `text` (used for speech and as translation source)
    translate: bool = True
    speak: bool = True


def build_blocks(data: dict, lang: str = "ru") -> list[Block]:
    """Turn the API JSON into display blocks. `lang` is the language of the entry itself."""
    blocks: list[Block] = []

    def add_sense(sense: dict, label: str, level: int):
        tags = sense.get("tags") or []
        prefix = f"{label} " + (f"[{', '.join(tags)}] " if tags else "")
        definition = (sense.get("definition") or "").strip()
        if definition:
            blocks.append(Block("def", definition, level, prefix, lang="en"))
        for ex in sense.get("examples") or []:
            if isinstance(ex, str) and ex.strip():
                blocks.append(Block("example", ex.strip(), level + 1, "› ", lang=lang))
        for q in sense.get("quotes") or []:
            text = q.get("text") if isinstance(q, dict) else None
            if text:
                blocks.append(Block("example", text.strip(), level + 1, "❝ ", lang=lang))
        if sense.get("synonyms"):
            blocks.append(Block("syn", ", ".join(sense["synonyms"]), level + 1, "Synonyms: ", lang=lang))
        if sense.get("antonyms"):
            blocks.append(Block("ant", ", ".join(sense["antonyms"]), level + 1, "Antonyms: ", lang=lang))
        trs = sense.get("translations") or []
        if trs:
            groups: dict[str, list[str]] = {}
            for t in trs:
                lname = (t.get("language") or {}).get("name") or (t.get("language") or {}).get("code", "?")
                groups.setdefault(lname, []).append(t.get("word", ""))
            text = "; ".join(f"{k}: {', '.join(v[:6])}" for k, v in list(groups.items())[:14])
            blocks.append(Block("trans", text, level + 1, "Translations — ", translate=False, speak=False))
        for i, sub in enumerate(sense.get("subsenses") or [], 1):
            add_sense(sub, f"{label.rstrip('.')}.{i}.", level + 1)

    for ent in data.get("entries") or []:
        pos = (ent.get("partOfSpeech") or "—").title()
        blocks.append(Block("pos", pos, lang="en"))
        prons = []
        for p in ent.get("pronunciations") or []:
            t = p.get("text")
            if t and t not in prons:
                prons.append(t)
        if prons:
            blocks.append(Block("ipa", "   ".join(prons[:4]), prefix="Pronunciation  ",
                                translate=False, speak=False))
        forms = []
        for f in ent.get("forms") or []:
            w = f.get("word")
            if w and w not in forms:
                forms.append(w)
        if forms:
            blocks.append(Block("forms", ", ".join(forms[:16]), prefix="Forms: ", translate=False, lang=lang))
        for n, sense in enumerate(ent.get("senses") or [], 1):
            add_sense(sense, f"{n}.", 0)
        if ent.get("synonyms"):
            blocks.append(Block("syn", ", ".join(ent["synonyms"]), prefix="Synonyms: ", lang=lang))
        if ent.get("antonyms"):
            blocks.append(Block("ant", ", ".join(ent["antonyms"]), prefix="Antonyms: ", lang=lang))
    if not blocks:
        blocks.append(Block("msg", "The response contains no entries.", translate=False, speak=False))
    return blocks


# --------------------------------------------------------------------------- translation
# Providers (Google, Microsoft, Lingva, MyMemory, LibreTranslate, Offline) with automatic fail-over
# live in translate_backends.py, next to this script.
from translate_backends import (Translator, Offline, PROVIDER_CHOICES, offline_available, offline_installed,  # noqa: E402
                                offline_plan, offline_install, offline_remove, offline_install_engine)


# --------------------------------------------------------------------------- text to speech
def split_for_tts(text: str, limit: int = 180) -> list[str]:
    pieces, cur = [], ""
    for word in text.split():
        if cur and len(cur) + 1 + len(word) > limit:
            pieces.append(cur)
            cur = word
        else:
            cur = f"{cur} {word}".strip()
    if cur:
        pieces.append(cur)
    return pieces or [text]

def tts_path(lang: str, text: str) -> Path:
    return TTS_DIR / (hashlib.sha1(f"{lang}|{text}".encode("utf-8")).hexdigest() + ".mp3")


def tts_fetch(lang: str, text: str, cancelled=lambda: False, save: bool = True) -> Path | None:
    """Return the Google TTS audio file (from the cache if present). None if cancelled meanwhile.
    With save=False a downloaded clip goes to a temporary file instead of the cache."""
    path = tts_path(lang, text)
    if path.exists() and path.stat().st_size > 0:
        return path
    audio = b""
    for piece in split_for_tts(text):
        if cancelled():
            return None
        q = urllib.parse.urlencode({
            "ie": "UTF-8", "client": "tw-ob", "tl": lang, "q": piece,
            "total": 1, "idx": 0, "textlen": len(piece),
        })
        req = urllib.request.Request(f"{GTTS_URL}?{q}", headers={"User-Agent": USER_AGENT})
        with urllib.request.urlopen(req, timeout=20) as resp:
            audio += resp.read()
    if not audio:
        raise RuntimeError("empty audio response")
    if not save:
        tmp = Path(tempfile.gettempdir()) / f"corpus_tts_{threading.get_ident()}.mp3"
        tmp.write_bytes(audio)
        return tmp
    TTS_DIR.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix(f".{threading.get_ident()}.part")
    tmp.write_bytes(audio)
    tmp.replace(path)
    return path

class Speaker:
    """Speaks text in a background thread. System voices (pyttsx3) or Google TTS.

    Everything that makes sound runs either in a child process (pyttsx3 worker, mpg123, ffplay,
    afplay ...) or is polled in the worker thread (Windows MCI, pygame), so `stop()` can always
    interrupt playback immediately: it bumps a generation counter and kills the child process.
    """

    def __init__(self, on_status):
        self.on_status = on_status
        self.q: queue.Queue = queue.Queue()
        self._gen = 0
        self._lock = threading.Lock()
        self._proc: subprocess.Popen | None = None
        threading.Thread(target=self._worker, daemon=True).start()

    # public ---------------------------------------------------------------
    def speak(self, text: str, lang: str, mode: str):
        self.stop()
        self.q.put((self._gen, text, lang, mode))

    def stop(self):
        with self._lock:
            self._gen += 1
            proc = self._proc
        if proc is not None and proc.poll() is None:
            try:
                proc.terminate()
            except Exception:
                pass

    # worker ---------------------------------------------------------------
    def _worker(self):
        while True:
            gen, text, lang, mode = self.q.get()
            if gen != self._gen:
                continue
            try:
                self._speak(gen, text, lang, mode)
            except Exception as e:  # report, never crash the thread
                if gen == self._gen:
                    self.on_status(f"Speech failed: {e}")

    def _speak(self, gen: int, text: str, lang: str, mode: str):
        text = text.strip()
        if not text:
            return
        if mode in ("Auto", "System voice"):
            if self._system(gen, text, lang):
                return
            if mode == "System voice":
                raise RuntimeError(
                    f"no system voice for '{lang}' (install one, or `pip install pyttsx3`)"
                )
        if gen != self._gen:
            return
        try:
            self._google(gen, text, lang)
        except (urllib.error.URLError, OSError) as e:
            raise RuntimeError(f"online speech unavailable ({e})")

    # child processes ------------------------------------------------------
    def _run(self, cmd: list[str], gen: int):
        """Run `cmd`, wait for it, and return its exit code (None if stopped before it started).
        The process handle is published so stop() can terminate it at any moment."""
        kwargs = {}
        if sys.platform == "win32":
            kwargs["creationflags"] = 0x08000000  # CREATE_NO_WINDOW
        with self._lock:
            if gen != self._gen:
                return None
            proc = subprocess.Popen(cmd, stdin=subprocess.DEVNULL, stdout=subprocess.DEVNULL,
                                    stderr=subprocess.DEVNULL, **kwargs)
            self._proc = proc
        try:
            return proc.wait()
        finally:
            with self._lock:
                if self._proc is proc:
                    self._proc = None

    # system voices --------------------------------------------------------
    @staticmethod
    def _find_voice(engine, lang: str):
        code = lang.split("-")[0].lower()
        name = LANG_NAMES.get(lang, LANG_NAMES.get(code, "")).split(" ")[0].lower()
        pattern = re.compile(rf"(^|[^a-z]){re.escape(code)}([^a-z]|$)")
        for v in engine.getProperty("voices"):
            langs = []
            for l in getattr(v, "languages", None) or []:
                langs.append(l.decode("utf-8", "ignore") if isinstance(l, bytes) else str(l))
            hay = " ".join([str(v.id), str(v.name)] + langs).lower()
            if pattern.search(hay) or (name and name in hay):
                return v
        return None

    def _system(self, gen: int, text: str, lang: str) -> bool:
        """Speak with pyttsx3 in a child process (so it can be killed). True if handled."""
        if importlib.util.find_spec("pyttsx3") is None:
            return False
        if getattr(sys, "frozen", False):
            cmd = [sys.executable, "--tts-worker", lang, text]
        else:
            cmd = [sys.executable, str(Path(__file__).resolve()), "--tts-worker", lang, text]
        try:
            rc = self._run(cmd, gen)
        except OSError:
            return False
        if rc is None or gen != self._gen:
            return True  # stopped on purpose: do not fall back to Google
        return rc == 0

    # google tts -----------------------------------------------------------
    def _google(self, gen: int, text: str, lang: str):
        path = tts_fetch(lang, text, lambda: gen != self._gen, offline_flag("do_tts", False))
        if path is None:
            return
        try:
            if gen == self._gen:
                self._play(path, gen)
        finally:
            if path != tts_path(lang, text):          # temporary, unsaved clip
                try:
                    path.unlink()
                except OSError:
                    pass

    def _play(self, path: Path, gen: int):
        if sys.platform == "win32":
            self._play_mci(path, gen)
            return
        if sys.platform == "darwin":
            self._run(["afplay", str(path)], gen)
            return
        for c in (["mpg123", "-q"], ["ffplay", "-nodisp", "-autoexit", "-loglevel", "quiet"],
                  ["mpv", "--no-video", "--really-quiet"], ["cvlc", "--play-and-exit", "--quiet"]):
            if shutil.which(c[0]):
                self._run(c + [str(path)], gen)
                return
        try:
            import pygame  # type: ignore
        except ImportError:
            raise RuntimeError("no audio player found (install mpg123, ffplay or mpv, or pygame)")
        pygame.mixer.init()
        pygame.mixer.music.load(str(path))
        pygame.mixer.music.play()
        while pygame.mixer.music.get_busy() and gen == self._gen:
            time.sleep(0.05)
        pygame.mixer.music.stop()

    def _play_mci(self, path: Path, gen: int):
        """Windows: play through MCI, polling so that stopping happens on this same thread."""
        import ctypes
        mci = ctypes.windll.winmm.mciSendStringW
        alias = f"rufd{int(time.time() * 1000)}"
        if mci(f'open "{path}" type mpegvideo alias {alias}', None, 0, None) != 0:
            raise RuntimeError("could not open the audio file")
        try:
            mci(f"play {alias}", None, 0, None)
            buf = ctypes.create_unicode_buffer(64)
            while gen == self._gen:
                mci(f"status {alias} mode", buf, 63, None)
                if buf.value != "playing":
                    break
                time.sleep(0.05)
        finally:
            mci(f"stop {alias}", None, 0, None)
            mci(f"close {alias}", None, 0, None)


def tts_worker_main(lang: str, text: str) -> int:
    """Entry point of the child process started by Speaker._system (exit 0 = spoken, 2 = unavailable)."""
    try:
        import pyttsx3
    except ImportError:
        return 2
    try:
        engine = pyttsx3.init()
        voice = Speaker._find_voice(engine, lang)
        if voice is None:
            return 2
        engine.setProperty("voice", voice.id)
        engine.say(text)
        engine.runAndWait()
        return 0
    except Exception:
        return 2


# --------------------------------------------------------------------------- the application
class App(tk.Tk):
    CHUNK = 2500

    def __init__(self):
        super().__init__()
        self.ui: dict = load_ui_settings()       # persisted window / widget state
        self._ui_ready = False                   # nothing is saved until the UI is built
        self._ui_job = None
        self.geometry(fit_geometry(self, self.ui.get("geometry"), "1380x840"))
        self.minsize(1100, 640)
        self.configure(bg=C["bg"])
        self._set_icon()

        self.q: queue.Queue = queue.Queue()
        self.code = load_last_dataset()          # data set key / folder name
        self.ds = DATASETS[self.code]
        self.lang = self.ds.lang                 # language code for speech + translation
        Offline.assume_source = ARGOS_MAP.get(self.lang, self.lang) if False else self.lang
        self.title(self.ds.title)
        self.targets = targets_for(self.lang)
        self.target_by_label = dict(self.targets)
        self._stores: dict = {}
        self.store, self.translator = self._open_dataset(self.code)
        self.speaker = Speaker(lambda m: self.q.put(("status", m)))
        self.flags: set[str] = self.store.load_flags()
        self.defined: set[str] = set()     # stored entry has definitions
        self.empty: set[str] = set()       # stored, but no entry (painted red)
        self._def_token = 0
        self.wordlist_path = wordlist_path(self.code)

        self.entries: list[Entry] = []
        self.keys: list[str] = []
        self.folds: list[str] = []
        self.view: list[Entry] = []
        col = self.ui.get("sort_col")
        self.sort_col = col if col in ("flag", "rank", "word", "freq") else "rank"
        self.sort_rev = bool(self.ui.get("sort_rev", False))

        self.current: Entry | None = None
        self.blocks: list[Block] = []
        self._inflight: set[str] = set()
        self._refresh_job = None
        self._select_job = None
        self._render_token = 0
        self._render_pos = 0
        self._tr_token = 0
        self._tab_msgs = {0: "", 1: "", 2: ""}     # status text per tab: Definitions / Translation / Raw JSON
        self._pending_rank = self.ui.get("last_rank", {}).get(self.code)   # word to re-select
        self._quiet_rank = None                                            # ...without speaking it

        self._setup_style()
        self._build_ui()
        self.bind("<Configure>", self._on_configure)
        self.protocol("WM_DELETE_WINDOW", self._on_close)
        self.after(80, self._poll_queue)
        self.after(60, self._load_words)
        self._ui_ready = True

    def _set_icon(self):
        try:
            self._icons = [tk.PhotoImage(data="".join(b.split())) for b in (ICON_256_B64, ICON_32_B64)]
            self.iconphoto(True, *self._icons)
        except tk.TclError:
            pass

    # ------------------------------------------------------------------ persistent UI state
    def _ui_choice(self, key: str, choices, default):
        v = self.ui.get(key)
        return v if v in choices else default

    def _ui_str(self, key: str) -> str:
        return str(self.ui.get(key, ""))

    def _ui_set(self, key: str, value):
        self.ui[key] = value
        self._save_ui_soon()

    def _saved_target(self) -> str:
        t = self.ui.get("targets", {}).get(self.code)
        return t if t in self.target_by_label else default_target(self.lang)

    def _collect_ui(self) -> dict:
        ui = self.ui
        try:
            ui["sash"] = self.pw.sash_coord(0)[0]
        except tk.TclError:
            pass
        try:
            ui["tab"] = self.nb.index(self.nb.select())
        except tk.TclError:
            pass
        ui.setdefault("targets", {})[self.code] = self.target_var.get()
        if self.current is not None:
            ui.setdefault("last_rank", {})[self.code] = self.current.rank
        ui.update(
            auto_translate=self.auto_translate.get(), auto_speak=self.auto_speak.get(),
            voice=self.voice_mode.get(), provider=self.provider_var.get(),
            search_field=self.search_field.get(), search_mode=self.search_mode.get(),
            search=self.search_var.get(), r_min=self.r_min.get(), r_max=self.r_max.get(),
            w_from=self.w_from.get(), w_to=self.w_to.get(), f_min=self.f_min.get(),
            f_max=self.f_max.get(), flag_filter=self.flag_filter.get(),
            sort_col=self.sort_col, sort_rev=self.sort_rev,
            def_filter=self.def_filter.get())
        return ui

    def _save_ui_soon(self, *_):
        if not self._ui_ready:
            return
        if self._ui_job:
            self.after_cancel(self._ui_job)
        self._ui_job = self.after(500, self._save_ui)

    def _save_ui(self):
        self._ui_job = None
        save_ui_settings(self._collect_ui())

    def _on_configure(self, e):
        if e.widget is self and self.state() == "normal":
            self.ui["geometry"] = self.geometry()
            self._save_ui_soon()

    def _remember_geometry(self, win, key: str):
        """Keep a pop-up window's size/position in the settings."""
        def on_cfg(e):
            if e.widget is win and win.state() == "normal":
                self.ui[key] = win.geometry()
                self._save_ui_soon()
        win.bind("<Configure>", on_cfg)

    def _place_sash(self, x: int):
        try:
            self.pw.sash_place(0, x, 1)
        except tk.TclError:
            pass

    def _on_close(self):
        try:
            self.speaker.stop()
            save_ui_settings(self._collect_ui())
        finally:
            self.destroy()

    # ------------------------------------------------------------------ data sets
    def _open_dataset(self, code: str):
        """(Store, Translator) for a data set; each is opened once and kept for the session."""
        if code not in self._stores:
            store = Store(db_path(code))
            self._stores[code] = (store, Translator(GatedStore(store)))
        return self._stores[code]

    def _on_dataset_selected(self, _event=None):
        label = self.dataset_var.get()
        code = next((c for c, ds in DATASETS.items() if ds.label == label), self.code)
        self.dataset_cb.selection_clear()
        self._switch_dataset(code)

    def _switch_dataset(self, code: str | None = None):
        code = code or self.code
        if code == self.code and self.entries:
            return
        self._collect_ui()
        self.speaker.stop()
        self._tr_token += 1
        self._render_token += 1
        self.code, self.ds = code, DATASETS[code]
        self.lang = self.ds.lang
        Offline.assume_source = ARGOS_MAP.get(self.lang, self.lang) if False else self.lang
        save_last_dataset(code)
        self.store, self.translator = self._open_dataset(code)
        self.flags = self.store.load_flags()
        self.defined, self.empty = set(), set()
        self._inflight.clear()
        self.current, self.blocks = None, []
        self._pending_rank = self.ui.get("last_rank", {}).get(code)
        self._quiet_rank = None
        self.entries, self.keys, self.folds, self.view = [], [], [], []
        self.tree.delete(*self.tree.get_children())
        for attr in ("_off_win", "_cov_win"):          # these windows belong to the old data set
            w = getattr(self, attr, None)
            if w is not None and w.winfo_exists():
                w.destroy()

        self.title(self.ds.title)
        self.targets = targets_for(self.lang)
        self.target_by_label = dict(self.targets)
        self.target_cb.configure(values=[t[0] for t in self.targets])
        self.target_var.set(self._saved_target())

        self._reset_filters()
        for job in (self._refresh_job, self._select_job):
            if job:
                self.after_cancel(job)
        self._refresh_job = self._select_job = None

        self.word_var.set("Select a word")
        self.meta_var.set("Pick an entry on the left to look it up.")
        self._message(self.def_text, "Select a word to see its definitions.")
        self._message(self.tr_text, "Press “Translate” to translate the word and the full response.")
        self._fill(self.raw_text, [], "r")
        self._load_words()

    # ------------------------------------------------------------------ style
    def _setup_style(self):
        s = ttk.Style(self)
        s.theme_use("clam")
        self.option_add("*TCombobox*Listbox.background", C["input"])
        self.option_add("*TCombobox*Listbox.foreground", C["text"])
        self.option_add("*TCombobox*Listbox.selectBackground", C["sel"])
        self.option_add("*TCombobox*Listbox.selectForeground", C["text"])
        self.option_add("*TCombobox*Listbox.font", FONT)

        s.configure(".", background=C["card"], foreground=C["text"], fieldbackground=C["input"],
                    bordercolor=C["border"], lightcolor=C["card"], darkcolor=C["card"],
                    troughcolor=C["bg"], focuscolor=C["card"], font=FONT)
        s.configure("TFrame", background=C["card"])
        s.configure("Bg.TFrame", background=C["bg"])
        s.configure("Panel.TFrame", background=C["panel"])
        s.configure("TLabel", background=C["card"], foreground=C["text"])
        s.configure("Muted.TLabel", foreground=C["muted"])
        s.configure("Section.TLabel", foreground=C["accent"], font=("Segoe UI", 9, "bold"))
        s.configure("Big.TLabel", font=("Segoe UI", 30, "bold"))
        s.configure("Status.TLabel", background=C["bg"], foreground=C["muted"], font=("Segoe UI", 9))

        s.configure("TButton", background=C["input"], foreground=C["text"], borderwidth=0,
                    padding=(12, 6), focusthickness=0, font=FONT)
        s.map("TButton", background=[("active", C["hover"]), ("pressed", C["sel"])])
        s.configure("Accent.TButton", background=C["accent"], foreground="#0b0e14", font=FONT_B)
        s.map("Accent.TButton", background=[("active", C["accent_hi"]), ("pressed", C["accent"])])
        s.configure("Flag.TButton", foreground=C["gold"], font=FONT_B)

        s.configure("TEntry", fieldbackground=C["input"], foreground=C["text"], insertcolor=C["text"],
                    bordercolor=C["border"], lightcolor=C["input"], darkcolor=C["input"], padding=5)
        s.map("TEntry", bordercolor=[("focus", C["accent"])])
        s.configure("Bad.TEntry", fieldbackground=C["bad"])

        s.configure("TCombobox", fieldbackground=C["input"], background=C["input"],
                    foreground=C["text"], arrowcolor=C["muted"], bordercolor=C["border"],
                    lightcolor=C["input"], darkcolor=C["input"], padding=5)
        s.map("TCombobox", fieldbackground=[("readonly", C["input"])],
              selectbackground=[("readonly", C["input"])], selectforeground=[("readonly", C["text"])],
              bordercolor=[("focus", C["accent"])])

        s.configure("TRadiobutton", background=C["card"], foreground=C["text"], indicatorcolor=C["input"])
        s.map("TRadiobutton", background=[("active", C["card"])], indicatorcolor=[("selected", C["accent"])])
        s.configure("TCheckbutton", background=C["card"], foreground=C["text"], indicatorcolor=C["input"])
        s.map("TCheckbutton", background=[("active", C["card"])], indicatorcolor=[("selected", C["accent"])])

        s.configure("Treeview", background=C["card"], fieldbackground=C["card"], foreground=C["text"],
                    rowheight=28, borderwidth=0, font=("Segoe UI", 11))
        s.map("Treeview", background=[("selected", C["sel"])], foreground=[("selected", "#ffffff")])
        s.configure("Treeview.Heading", background=C["panel"], foreground=C["muted"], relief="flat",
                    font=("Segoe UI", 9, "bold"), padding=(8, 7))
        s.map("Treeview.Heading", background=[("active", C["hover"])], foreground=[("active", C["text"])])

        s.configure("TNotebook", background=C["card"], borderwidth=0, tabmargins=(0, 0, 0, 0))
        s.configure("TNotebook.Tab", background=C["panel"], foreground=C["muted"], padding=(18, 8),
                    borderwidth=0, font=FONT_B)
        s.map("TNotebook.Tab", background=[("selected", C["card"]), ("active", C["hover"])],
              foreground=[("selected", C["accent"]), ("active", C["text"])])

        for orient in ("Vertical", "Horizontal"):
            s.configure(f"{orient}.TScrollbar", background=C["input"], troughcolor=C["card"],
                        bordercolor=C["card"], arrowcolor=C["muted"], lightcolor=C["input"],
                        darkcolor=C["input"], relief="flat", arrowsize=12)
            s.map(f"{orient}.TScrollbar", background=[("active", C["hover"])])

    # ------------------------------------------------------------------ UI
    def _build_ui(self):
        root = ttk.Frame(self, style="Bg.TFrame", padding=10)
        root.pack(fill="both", expand=True)
        root.rowconfigure(0, weight=1)
        root.columnconfigure(0, weight=1)

        self.pw = pw = tk.PanedWindow(root, orient="horizontal", bg=C["bg"], sashwidth=10, bd=0, sashrelief="flat")
        pw.grid(row=0, column=0, sticky="nsew")
        left = ttk.Frame(pw, padding=14)
        right = ttk.Frame(pw, padding=14)
        pw.add(left, minsize=560, width=640)
        pw.add(right, minsize=500)
        sash = self.ui.get("sash")
        if isinstance(sash, int) and 560 <= sash <= 3000:
            self.after(150, lambda: self._place_sash(sash))
        pw.bind("<ButtonRelease-1>", self._save_ui_soon)

        self._build_left(left)
        self._build_right(right)

        bar = ttk.Frame(root, style="Bg.TFrame")
        bar.grid(row=1, column=0, sticky="ew", pady=(8, 0))
        bar.columnconfigure(0, weight=1)
        self.status = tk.StringVar(value="Starting…")
        ttk.Label(bar, textvariable=self.status, style="Status.TLabel").grid(row=0, column=0, sticky="w")
        ttk.Label(bar, style="Status.TLabel",
                  text="Definitions: Wiktionary (CC BY-SA 4.0) via FreeDictionaryAPI.com  ·  "
                       "Translation: Google / Microsoft / Lingva / MyMemory  ·  Online voice: Google").grid(row=0, column=1, sticky="e")

        self.bind("<Control-f>", lambda e: (self.search_entry.focus_set(), self.search_entry.select_range(0, "end")))

    def _build_left(self, f: ttk.Frame):
        f.columnconfigure(0, weight=1)
        f.rowconfigure(3, weight=1)

        # --- data set selector + search heading
        hdr = ttk.Frame(f)
        hdr.grid(row=0, column=0, sticky="ew")
        hdr.columnconfigure(0, weight=1)
        ttk.Label(hdr, text="SEARCH", style="Section.TLabel").grid(row=0, column=0, sticky="w")
        ttk.Label(hdr, text="DATA SET", style="Section.TLabel").grid(row=0, column=1, padx=(0, 10))
        self.dataset_var = tk.StringVar(value=self.ds.label)
        self.dataset_cb = ttk.Combobox(hdr, textvariable=self.dataset_var, state="readonly", width=20,
                                       values=[ds.label for ds in DATASETS.values()])
        self.dataset_cb.grid(row=0, column=2)
        self.dataset_cb.bind("<<ComboboxSelected>>", self._on_dataset_selected)

        # --- search
        sf = ttk.Frame(f)
        sf.grid(row=1, column=0, sticky="ew", pady=(4, 12))
        sf.columnconfigure(2, weight=1)
        self.search_field = tk.StringVar(value=self._ui_choice("search_field", ("Word", "Rank", "Frequency"), "Word"))
        self.search_mode = tk.StringVar(value=self._ui_choice(
            "search_mode", ("Contains", "Starts with", "Ends with", "Exact"), "Contains"))
        self.search_var = tk.StringVar(value=self._ui_str("search"))
        ttk.Combobox(sf, textvariable=self.search_field, values=["Word", "Rank", "Frequency"],
                     state="readonly", width=10).grid(row=0, column=0, padx=(0, 6))
        ttk.Combobox(sf, textvariable=self.search_mode,
                     values=["Contains", "Starts with", "Ends with", "Exact"],
                     state="readonly", width=11).grid(row=0, column=1, padx=(0, 6))
        self.search_entry = ttk.Entry(sf, textvariable=self.search_var, font=("Segoe UI", 11))
        self.search_entry.grid(row=0, column=2, sticky="ew")
        ttk.Button(sf, text="✕", width=3, command=lambda: self.search_var.set("")).grid(row=0, column=3, padx=(6, 0))

        # --- filters
        ff = ttk.Frame(f)
        ff.grid(row=2, column=0, sticky="ew", pady=(0, 10))
        ttk.Label(ff, text="FILTERS", style="Section.TLabel").grid(row=0, column=0, columnspan=6, sticky="w", pady=(0, 4))
        self.r_min, self.r_max = tk.StringVar(value=self._ui_str("r_min")), tk.StringVar(value=self._ui_str("r_max"))
        self.w_from, self.w_to = tk.StringVar(value=self._ui_str("w_from")), tk.StringVar(value=self._ui_str("w_to"))
        self.f_min, self.f_max = tk.StringVar(value=self._ui_str("f_min")), tk.StringVar(value=self._ui_str("f_max"))
        self.flag_filter = tk.StringVar(value=self._ui_choice("flag_filter", ("All", "Flagged", "Unflagged"), "All"))
        self.filter_entries: dict[str, ttk.Entry] = {}
        self.def_filter = tk.StringVar(value=self._ui_choice("def_filter", ("All", "Defined", "Undefined"), "All"))

        def row(r, label, a, b, la, lb, hint=""):
            ttk.Label(ff, text=label).grid(row=r, column=0, sticky="w", pady=3)
            ttk.Label(ff, text=la, style="Muted.TLabel").grid(row=r, column=1, padx=(10, 4))
            ea = ttk.Entry(ff, textvariable=a, width=11)
            ea.grid(row=r, column=2)
            ttk.Label(ff, text=lb, style="Muted.TLabel").grid(row=r, column=3, padx=(10, 4))
            eb = ttk.Entry(ff, textvariable=b, width=11)
            eb.grid(row=r, column=4)
            if hint:
                ttk.Label(ff, text=hint, style="Muted.TLabel").grid(row=r, column=5, padx=(10, 0), sticky="w")
            self.filter_entries[str(a)] = ea
            self.filter_entries[str(b)] = eb

        row(1, "Rank", self.r_min, self.r_max, "min", "max", "e.g. 1 – 100")
        row(2, "Word", self.w_from, self.w_to, "from", "to", "e.g. a – m")
        row(3, "Frequency", self.f_min, self.f_max, "min", "max")

        fl = ttk.Frame(ff)
        fl.grid(row=4, column=0, columnspan=6, sticky="ew", pady=(8, 0))
        ttk.Label(fl, text="Flag", width=11).pack(side="left")
        for txt in ("All", "Flagged", "Unflagged"):
            ttk.Radiobutton(fl, text=txt, value=txt, variable=self.flag_filter).pack(side="left", padx=(0, 12))
        ttk.Button(fl, text="Reset", command=self._reset_filters).pack(side="right")

        dl = ttk.Frame(ff)
        dl.grid(row=5, column=0, columnspan=6, sticky="ew", pady=(4, 0))
        ttk.Label(dl, text="Definitions", width=11).pack(side="left")
        for txt in ("All", "Defined", "Undefined"):
            ttk.Radiobutton(dl, text=txt, value=txt, variable=self.def_filter).pack(side="left", padx=(0, 12))
        fl.grid(row=4, column=0, columnspan=6, sticky="ew", pady=(8, 0))

        for v in (self.search_var, self.search_field, self.search_mode, self.r_min, self.r_max,
                  self.w_from, self.w_to, self.f_min, self.f_max, self.flag_filter, self.def_filter):
            v.trace_add("write", self._schedule_refresh)
            v.trace_add("write", self._save_ui_soon)

        # --- table
        tf = ttk.Frame(f)
        tf.grid(row=3, column=0, sticky="nsew")
        tf.rowconfigure(0, weight=1)
        tf.columnconfigure(0, weight=1)
        self.tree = ttk.Treeview(tf, columns=("flag", "rank", "word", "freq"), show="headings",
                                 selectmode="extended")
        for col, text, w, anchor in (("flag", "⚑", 46, "center"), ("rank", "Rank", 90, "e"),
                                     ("word", "Word", 250, "w"), ("freq", "Frequency", 130, "e")):
            self.tree.heading(col, text=text, command=lambda c=col: self._sort_by(c))
            self.tree.column(col, width=w, anchor=anchor, stretch=(col == "word"))
        self.tree.tag_configure("even", background=C["card"])
        self.tree.tag_configure("odd", background=C["stripe"])
        self.tree.tag_configure("flag", foreground=C["gold"])
        self.tree.tag_configure("empty", background=C["empty"])
        sb = ttk.Scrollbar(tf, orient="vertical", command=self.tree.yview)
        self.tree.configure(yscrollcommand=sb.set)
        self.tree.grid(row=0, column=0, sticky="nsew")
        sb.grid(row=0, column=1, sticky="ns")
        self.tree.bind("<<TreeviewSelect>>", self._on_select)
        self.tree.bind("<Button-1>", self._on_tree_click)
        self.tree.bind("<Double-1>", self._on_tree_double)
        self.tree.bind("<Return>", lambda e: self._speak_word())
        self.tree.bind("<f>", lambda e: self._toggle_flag())
        self.tree.bind("<Control-c>", self._copy_words)

        bf = ttk.Frame(f)
        bf.grid(row=4, column=0, sticky="ew", pady=(10, 0))
        bf.columnconfigure(0, weight=1)
        self.count_var = tk.StringVar()
        ttk.Label(bf, textvariable=self.count_var, style="Muted.TLabel").grid(row=0, column=0, sticky="w")
        bf.columnconfigure(1, weight=0)
        ttk.Button(bf, text="📝  Translate text", command=self._open_translator).grid(row=0, column=1, sticky="e", padx=(0, 8))
        ttk.Button(bf, text="📥  Offline mode", command=self._open_offline_mode).grid(row=0, column=2, sticky="e", padx=(0, 8))
        ttk.Button(bf, text="📊  Coverage", command=self._open_coverage).grid(row=0, column=3, sticky="e")

    def _build_right(self, f: ttk.Frame):
        f.columnconfigure(0, weight=1)
        f.rowconfigure(3, weight=1)

        head = ttk.Frame(f)
        head.grid(row=0, column=0, sticky="ew")
        head.columnconfigure(0, weight=1)
        self.word_var = tk.StringVar(value="Select a word")
        self.meta_var = tk.StringVar(value="Pick an entry on the left to look it up.")
        ttk.Label(head, textvariable=self.word_var, style="Big.TLabel").grid(row=0, column=0, sticky="w")
        ttk.Label(head, textvariable=self.meta_var, style="Muted.TLabel").grid(row=1, column=0, sticky="w")
        btns = ttk.Frame(head)
        btns.grid(row=0, column=1, rowspan=2, sticky="e")
        ttk.Button(btns, text="🔊  Speak", style="Accent.TButton", command=self._speak_word).pack(side="left", padx=4)
        ttk.Button(btns, text="■", width=3, command=self._stop_speech).pack(side="left", padx=4)
        self.head_flag_btn = ttk.Button(btns, text="⚑  Flag", style="Flag.TButton", command=self._toggle_flag)
        self.head_flag_btn.pack(side="left", padx=4)
        ttk.Button(btns, text="⟳  Refresh", command=lambda: self._load_entry(force=True)).pack(side="left", padx=4)

        # options row
        of = ttk.Frame(f)
        of.grid(row=1, column=0, sticky="ew", pady=(14, 8))
        ttk.Label(of, text="Translate to", style="Muted.TLabel").pack(side="left")
        self.target_var = tk.StringVar(value=self._saved_target())
        self.target_cb = ttk.Combobox(of, textvariable=self.target_var, values=[t[0] for t in self.targets],
                                      state="readonly", width=22)
        self.target_cb.pack(side="left", padx=(8, 8))
        ttk.Button(of, text="🌐  Translate", command=lambda: self._start_translate(show_tab=True)).pack(side="left")
        self.auto_translate = tk.BooleanVar(value=bool(self.ui.get("auto_translate", False)))
        ttk.Checkbutton(of, text="auto", variable=self.auto_translate,
                        command=lambda: self.auto_translate.get() and self._start_translate()).pack(side="left", padx=(10, 0))

        self.voice_mode = tk.StringVar(value=self._ui_choice(
            "voice", ("Auto", "System voice", "Google (online)"), "Auto"))
        ttk.Combobox(of, textvariable=self.voice_mode, values=["Auto", "System voice", "Google (online)"],
                     state="readonly", width=14).pack(side="right")
        ttk.Label(of, text="Voice", style="Muted.TLabel").pack(side="right", padx=(0, 8))
        self.auto_speak = tk.BooleanVar(value=bool(self.ui.get("auto_speak", False)))
        ttk.Checkbutton(of, text="speak on select", variable=self.auto_speak).pack(side="right", padx=(0, 16))

        hint = ttk.Frame(f)
        hint.grid(row=2, column=0, sticky="ew", pady=(0, 6))
        hint.columnconfigure(0, weight=1)
        ttk.Label(hint, text="Click any definition, example or translation to hear it.",
                  style="Muted.TLabel").grid(row=0, column=0, sticky="w")
        ttk.Label(hint, text="Translate via", style="Muted.TLabel").grid(row=0, column=1, padx=(8, 6))
        self.provider_var = tk.StringVar(value=self._ui_choice("provider", PROVIDER_CHOICES, "Auto"))
        cb = ttk.Combobox(hint, textvariable=self.provider_var, values=PROVIDER_CHOICES,
                          state="readonly", width=15)
        cb.grid(row=0, column=2)
        cb.bind("<<ComboboxSelected>>", self._on_provider_change)

        self.nb = ttk.Notebook(f)
        self.nb.grid(row=3, column=0, sticky="nsew")
        self.def_text = self._make_text(self.nb, "Definitions")
        self.tr_text = self._make_text(self.nb, "Translation")
        self.raw_text = self._make_text(self.nb, "Raw JSON", mono=True)
        self._message(self.def_text, "Select a word to see its definitions.")
        self._message(self.tr_text, "Press “Translate” to translate the word and the full response.")
        tab = self.ui.get("tab")
        if isinstance(tab, int) and 0 <= tab < 3:
            self.nb.select(tab)
        self.nb.bind("<<NotebookTabChanged>>", self._on_tab_changed)
        for v in (self.target_var, self.auto_translate, self.auto_speak, self.voice_mode, self.provider_var):
            v.trace_add("write", self._save_ui_soon)

    def _make_text(self, nb: ttk.Notebook, title: str, mono: bool = False) -> tk.Text:
        frame = ttk.Frame(nb)
        frame.rowconfigure(0, weight=1)
        frame.columnconfigure(0, weight=1)
        t = tk.Text(frame, wrap="word", bg=C["card"], fg=C["text"], bd=0, highlightthickness=0,
                    padx=16, pady=10, insertbackground=C["text"], selectbackground=C["sel"],
                    selectforeground="#ffffff", font=MONO if mono else ("Segoe UI", 11),
                    spacing1=2, cursor="arrow")
        sb = ttk.Scrollbar(frame, orient="vertical", command=t.yview)
        t.configure(yscrollcommand=sb.set)
        t.grid(row=0, column=0, sticky="nsew")
        sb.grid(row=0, column=1, sticky="ns")
        nb.add(frame, text=title)
        sg = ("Segoe UI", 11)
        t.tag_configure("k_pos", font=("Segoe UI", 12, "bold"), foreground=C["accent"], spacing1=16, spacing3=4)
        t.tag_configure("k_ipa", foreground=C["muted"], font=MONO)
        t.tag_configure("k_forms", foreground=C["muted"], font=("Segoe UI", 10))
        t.tag_configure("k_def", font=("Segoe UI", 12), spacing1=8, spacing3=2)
        t.tag_configure("k_example", font=("Segoe UI", 11, "italic"), foreground="#b8c1d6")
        t.tag_configure("k_syn", foreground=C["green"], font=sg)
        t.tag_configure("k_ant", foreground=C["red"], font=sg)
        t.tag_configure("k_trans", foreground=C["muted"], font=("Segoe UI", 10))
        t.tag_configure("k_head", font=("Segoe UI", 20, "bold"), foreground=C["accent"], spacing1=4, spacing3=6)
        t.tag_configure("k_alt", font=sg)
        t.tag_configure("k_msg", foreground=C["muted"], font=("Segoe UI", 11, "italic"))
        for lv in range(4):
            t.tag_configure(f"lv{lv}", lmargin1=18 * lv, lmargin2=18 * lv + 24)
        t.tag_configure("prefix", foreground=C["muted"], font=("Segoe UI", 10))
        t.configure(state="disabled")
        return t

    def _cur_tab(self) -> int:
        try:
            return self.nb.index(self.nb.select())
        except tk.TclError:
            return 0

    def _tab_status(self, text: str, *tabs: int):
        """Store `text` as the status of the given tabs; show it now if one of them is selected."""
        for t in tabs:
            self._tab_msgs[t] = text
        if self._cur_tab() in tabs:
            self.status.set(text)

    def _on_tab_changed(self, _event=None):
        text = self._tab_msgs.get(self._cur_tab(), "")
        if text:
            self.status.set(text)
        self._save_ui_soon()

    def _reset_tab_status(self, word: str):
        self._tab_status(f"Definitions: looking up “{word}” …", 0)
        self._tab_status(f"Translation: press “Translate” to translate “{word}”", 1)
        self._tab_status(f"Raw JSON: waiting for the entry for “{word}”", 2)

    # ------------------------------------------------------------------ text rendering
    def _message(self, widget: tk.Text, msg: str):
        self._fill(widget, [Block("msg", msg, translate=False, speak=False)], "m")

    def _fill(self, widget: tk.Text, blocks: list[Block], tagprefix: str):
        widget.configure(state="normal")
        widget.delete("1.0", "end")
        for t in widget.tag_names():
            if t.startswith("c_"):
                widget.tag_delete(t)
        for i, b in enumerate(blocks):
            base = (f"k_{b.kind}", f"lv{min(b.level, 3)}")
            if b.prefix:
                widget.insert("end", b.prefix, base + ("prefix",))
            if b.speak:
                tag = f"c_{tagprefix}{i}"
                widget.insert("end", b.text, base + (tag,))
                widget.tag_bind(tag, "<Button-1>", lambda e, t=b.text, l=b.lang: self._speak(t, l))
                widget.tag_bind(tag, "<Enter>", lambda e, w=widget, tg=tag: (
                    w.tag_configure(tg, background=C["hover"]), w.configure(cursor="hand2")))
                widget.tag_bind(tag, "<Leave>", lambda e, w=widget, tg=tag: (
                    w.tag_configure(tg, background=""), w.configure(cursor="arrow")))
            else:
                widget.insert("end", b.text, base)
            widget.insert("end", "\n", base)
        widget.configure(state="disabled")
        widget.yview_moveto(0)

    # ------------------------------------------------------------------ word list
    def _load_words(self):
        code = self.code
        ds = self.ds
        path = self.wordlist_path = wordlist_path(code)
        if not path.exists():
            path.parent.mkdir(parents=True, exist_ok=True)
            for cand in (APP_DIR / ds.wordlist, DATA_DIR / ds.wordlist, Path.cwd() / ds.wordlist):
                if cand.exists():
                    shutil.copyfile(cand, path)
                    break
            else:
                messagebox.showinfo("Word list needed",
                                    f"Could not find {path}.\nPlease select your {ds.wordlist} file; "
                                    "it will be copied into the data folder.")
                p = filedialog.askopenfilename(title=f"Select {ds.wordlist}",
                                               filetypes=[("Text", "*.txt"), ("All files", "*.*")])
                if not p:
                    self._update_count()
                    self.status.set(f"No word list loaded for {ds.label}. Switch data set to retry.")
                    return
                shutil.copyfile(p, path)
        try:
            self.entries = load_wordlist(path)
        except Exception as e:
            messagebox.showerror("Error", f"Could not read the word list:\n{e}")
            return
        self.keys = [alpha_key(e.word, code) for e in self.entries]
        self.folds = [fold(e.word, code) for e in self.entries]
        self.status.set(f"Loaded {len(self.entries):,} words from {path.parent.name}/{path.name}")
        self.refresh()
        self._scan_definitions()

    # ------------------------------------------------------------------ filtering / sorting
    def _schedule_refresh(self, *_):
        if self._refresh_job:
            self.after_cancel(self._refresh_job)
        self._refresh_job = self.after(250, self.refresh)

    def _reset_filters(self):
        for v in (self.search_var, self.r_min, self.r_max, self.w_from, self.w_to, self.f_min, self.f_max):
            v.set("")
        self.flag_filter.set("All")
        self.def_filter.set("All")

    def _mark(self, var: tk.StringVar, ok: bool):
        e = self.filter_entries.get(str(var))
        if e:
            e.configure(style="TEntry" if ok else "Bad.TEntry")

    def _num(self, var: tk.StringVar):
        s = re.sub(r"[\s,_]", "", var.get())
        if not s:
            self._mark(var, True)
            return None
        try:
            v = int(s)
        except ValueError:
            self._mark(var, False)
            return None
        self._mark(var, True)
        return v

    def refresh(self):
        self._refresh_job = None
        if not self.entries:
            return
        rmin, rmax = self._num(self.r_min), self._num(self.r_max)
        fmin, fmax = self._num(self.f_min), self._num(self.f_max)
        wlo = alpha_key(self.w_from.get().strip(), self.code)
        whi = alpha_key(self.w_to.get().strip(), self.code)
        flag_mode = self.flag_filter.get()
        def_mode = self.def_filter.get()
        defined, empty = self.defined, self.empty

        field = self.search_field.get()
        mode = self.search_mode.get()
        query = self.search_var.get().strip()
        query = fold(query, self.code) if field == "Word" else re.sub(r"[\s,_]", "", query)
        match = {
            "Contains": lambda h: query in h,
            "Starts with": lambda h: h.startswith(query),
            "Ends with": lambda h: h.endswith(query),
            "Exact": lambda h: h == query,
        }[mode]

        flags = self.flags
        keys, folds = self.keys, self.folds
        out: list[Entry] = []
        for i, e in enumerate(self.entries):
            if rmin is not None and e.rank < rmin:
                continue
            if rmax is not None and e.rank > rmax:
                continue
            if fmin is not None and e.freq < fmin:
                continue
            if fmax is not None and e.freq > fmax:
                continue
            if wlo or whi:
                k = keys[i]
                if wlo and k < wlo:
                    continue
                if whi and k[: len(whi)] > whi:
                    continue
            if flag_mode != "All" and ((e.word in flags) != (flag_mode == "Flagged")):
                continue
            if def_mode == "Defined" and e.word not in defined:
                continue
            if def_mode == "Undefined" and e.word not in empty:
                continue
            if query:
                hay = folds[i] if field == "Word" else str(e.rank if field == "Rank" else e.freq)
                if not match(hay):
                    continue
            out.append(e)
        self.view = out
        self._apply_sort()
        self._render_view()

    def _sort_by(self, col: str):
        if self.sort_col == col:
            self.sort_rev = not self.sort_rev
        else:
            self.sort_col, self.sort_rev = col, (col in ("freq", "flag"))
        self._apply_sort()
        self._render_view()
        self._save_ui_soon()

    def _apply_sort(self):
        col, rev = self.sort_col, self.sort_rev
        if col == "rank":
            self.view.sort(key=lambda e: e.rank, reverse=rev)
        elif col == "freq":
            self.view.sort(key=lambda e: e.freq, reverse=rev)
        elif col == "word":
            self.view.sort(key=lambda e: self.keys[e.rank - 1], reverse=rev)
        else:  # flag
            self.view.sort(key=lambda e: (e.word in self.flags, -e.rank), reverse=rev)
        names = {"flag": "⚑", "rank": "Rank", "word": "Word", "freq": "Frequency"}
        for c, n in names.items():
            arrow = (" ▼" if rev else " ▲") if c == col else ""
            self.tree.heading(c, text=n + arrow)

    def _row_values(self, e: Entry):
        return ("⚑" if e.word in self.flags else "", f"{e.rank:,}", e.word, f"{e.freq:,}")

    def _row_tags(self, e: Entry, n: int) -> tuple:
        bg = "empty" if e.word in self.empty else ("odd" if n % 2 else "even")
        return (bg, "flag") if e.word in self.flags else (bg,)

    def _render_view(self):
        self._render_token += 1
        self.tree.delete(*self.tree.get_children())
        self._render_pos = 0
        self._update_count()
        self._render_chunk(self._render_token)

    def _render_chunk(self, token: int):
        if token != self._render_token:
            return
        view, pos = self.view, self._render_pos
        end = min(pos + self.CHUNK, len(view))
        for n in range(pos, end):
            e = view[n]
            tags = self._row_tags(e, n)
            self.tree.insert("", "end", iid=str(e.rank), values=self._row_values(e), tags=tags)
        self._render_pos = end
        if end < len(view):
            self.after(1, self._render_chunk, token)
        elif self.current and self.tree.exists(str(self.current.rank)):
            iid = str(self.current.rank)
            self.tree.selection_set(iid)
            self.tree.see(iid)
        elif self._pending_rank is not None:            # re-select the word from the last session
            rank, self._pending_rank = self._pending_rank, None
            if self.tree.exists(str(rank)):
                self._quiet_rank = rank
                self.tree.selection_set(str(rank))
                self.tree.see(str(rank))

    def _update_count(self):
        self.count_var.set(f"{len(self.view):,} of {len(self.entries):,} shown   ·   "
                           f"{len(self.flags):,} flagged   ·   {len(self.empty):,} undefined")

    # ------------------------------------------------------------------ stored definitions
    def _scan_definitions(self):
        """Check every stored dictionary entry in the background (see scan_definitions)."""
        self._def_token += 1
        token, code, path = self._def_token, self.code, db_path(self.code)

        def work():
            try:
                res = scan_definitions(path)
            except Exception:
                res = None
            self.q.put(("call", self._on_definitions_scanned, token, code, res))

        threading.Thread(target=work, daemon=True).start()

    def _on_definitions_scanned(self, token, code, res):
        if res is None or token != self._def_token or code != self.code:
            return
        self.defined, self.empty = res
        if self.def_filter.get() == "All":
            for n, iid in enumerate(self.tree.get_children()):      # recolour in place
                self.tree.item(iid, tags=self._row_tags(self.entries[int(iid) - 1], n))
            self._update_count()
        else:
            self.refresh()

    def _mark_defined(self, word: str, has: bool):
        """A lookup just stored (or read) this word: update the sets and its row."""
        (self.defined if has else self.empty).add(word)
        (self.empty if has else self.defined).discard(word)
        e = self.current
        if e is not None and e.word == word and self.tree.exists(str(e.rank)):
            iid = str(e.rank)
            self.tree.item(iid, tags=self._row_tags(e, self.tree.index(iid)))
        self._update_count()

    # ------------------------------------------------------------------ selection / flags
    def _selected_entries(self) -> list[Entry]:
        return [self.entries[int(i) - 1] for i in self.tree.selection()]

    def _on_select(self, _event=None):
        sel = self.tree.selection()
        if not sel:
            return
        focus = self.tree.focus()
        iid = focus if focus in sel else sel[-1]
        e = self.entries[int(iid) - 1]
        self._update_flag_buttons()
        if self.current is not None and self.current.rank == e.rank:
            return
        self.current = e
        self._reset_tab_status(e.word)
        self.word_var.set(e.word)
        self.meta_var.set(f"Rank #{e.rank:,}   ·   {e.freq:,} occurrences")
        if self.auto_speak.get() and self._quiet_rank != e.rank:
            self._speak(e.word, self.lang)
        self._quiet_rank = None
        self.ui.setdefault("last_rank", {})[self.code] = e.rank
        self._save_ui_soon()
        if self._select_job:
            self.after_cancel(self._select_job)
        self._select_job = self.after(220, self._load_entry)  # debounce fast scrolling

    def _on_tree_click(self, event):
        if self.tree.identify_region(event.x, event.y) == "cell" and self.tree.identify_column(event.x) == "#1":
            iid = self.tree.identify_row(event.y)
            if iid:
                self._toggle_flag([iid])
                return "break"

    def _on_tree_double(self, event):
        if self.tree.identify_column(event.x) != "#1" and self.tree.identify_row(event.y):
            self._speak_word()

    def _copy_words(self, _event=None):
        words = "\n".join(e.word for e in self._selected_entries())
        if words:
            self.clipboard_clear()
            self.clipboard_append(words)
            self.status.set("Copied selected words to the clipboard")

    def _toggle_flag(self, iids=None):
        iids = list(iids or self.tree.selection())
        if not iids:
            return
        words = [self.entries[int(i) - 1].word for i in iids]
        unflagged = [w for w in words if w not in self.flags]
        if unflagged:
            self.flags.update(unflagged)
            self.store.set_flags(unflagged, True)
            self.status.set(f"Flagged {len(unflagged)} word(s)")
        else:
            self.flags.difference_update(words)
            self.store.set_flags(words, False)
            self.status.set(f"Unflagged {len(words)} word(s)")
        if self.flag_filter.get() != "All" or self.sort_col == "flag":
            self.refresh()
        else:
            for i in iids:
                if self.tree.exists(i):
                    e = self.entries[int(i) - 1]
                    n = self.tree.index(i)
                    tags = ("odd" if n % 2 else "even",) + (("flag",) if e.word in self.flags else ())
                    self.tree.item(i, values=self._row_values(e), tags=tags)
            self._update_count()
        self._update_flag_buttons()

    def _update_flag_buttons(self):
        ents = self._selected_entries()
        if not ents:
            ents = [self.current] if self.current else []
        if not ents:
            return
        any_unflagged = any(e.word not in self.flags for e in ents)
        n = f" ({len(ents)})" if len(ents) > 1 else ""
        self.head_flag_btn.configure(text=("⚑  Flag" if any_unflagged else "⚑  Unflag") + n)

    # ------------------------------------------------------------------ dictionary lookup
    def _load_entry(self, force: bool = False):
        self._select_job = None
        e = self.current
        if e is None:
            return
        word = e.word
        if not force:
            cached = self.store.get_entry(word)
            if cached:
                self._on_entry(word, cached[0], cached[1], True)
                return
        if word in self._inflight:
            return
        self._inflight.add(word)
        self._message(self.def_text, f"Fetching “{word}” from freedictionaryapi.com …")
        self._tab_status(f"Definitions: requesting “{word}” from freedictionaryapi.com …", 0, 2)
        threading.Thread(target=self._fetch_worker,
                         args=(word, self.code, self.ds.dict_lang, self.store), daemon=True).start()

    def _fetch_worker(self, word: str, code: str, dict_lang: str, store: Store):
        try:
            status, body = fetch_entry(word, dict_lang)
            if status in (200, 404):
                saved = offline_flag("do_defs")
                if saved:
                    store.put_entry(word, status, body)
                msg = ("entry", word, status, body, False, saved)
            elif status == 429:
                msg = ("entry_err", word, "Rate limit reached (1,000 requests/hour). Try again later.")
            else:
                msg = ("entry_err", word, f"Server returned HTTP {status}.")
        except Exception as e:
            msg = ("entry_err", word, f"Offline or unreachable and not cached yet ({e}).")
        if code == self.code:
            self.q.put(msg)

    def _on_entry(self, word: str, status: int, body: str, cached: bool, saved: bool = True):
        self._inflight.discard(word)
        if self.current is None or self.current.word != word:
            return
        has = False
        if status == 404:
            self.blocks = [Block("msg", "No dictionary entry found for this word.", translate=False, speak=False)]
            raw = body
        else:
            try:
                data = json.loads(body)
                self.blocks = build_blocks(data, self.lang)
                has = bool(isinstance(data, dict) and data.get("entries"))
                raw = json.dumps(data, ensure_ascii=False, indent=2)
            except json.JSONDecodeError:
                self.blocks = [Block("msg", "The response could not be parsed.", translate=False, speak=False)]
                raw = body
        if cached or saved:
            self._mark_defined(word, has)
        self._fill(self.def_text, self.blocks, "d")
        self._fill(self.raw_text, [Block("msg", raw, translate=False, speak=False)], "r")
        self.raw_text.tag_configure("k_msg", font=MONO, foreground=C["text"])
        db = f"data/lang/{self.code}/dictionary.db"
        if cached:
            how = f"loaded from the local cache ({db})"
        elif saved:
            how = f"fetched online and saved to {db}"
        else:
            how = "fetched online, not saved (Offline mode → Definitions is unchecked)"
        self._tab_status(f"Definitions: “{word}” {how}", 0)
        self._tab_status(f"Raw JSON: “{word}” {how}", 2)
        if self.auto_translate.get():
            self._start_translate()
        else:
            self._message(self.tr_text, "Press “Translate” to translate the word and the full response.")

    # ------------------------------------------------------------------ translation
    def _target(self) -> str:
        return self.target_by_label.get(self.target_var.get(), "en")

    def _start_translate(self, show_tab: bool = False, refresh: bool = False):
        if self.current is None:
            return
        if show_tab:
            self.nb.select(1)
        word, tl, blocks = self.current.word, self._target(), list(self.blocks)
        provider = self.provider_var.get()
        self._tr_token += 1
        self._message(self.tr_text, f"Translating to {self.target_var.get()} via {provider} …")
        self._tab_status(f"Translation: translating “{word}” via {provider} …", 1)
        threading.Thread(target=self._translate_worker,
                         args=(word, tl, blocks, provider, refresh, self._tr_token,
                               self.translator, self.lang), daemon=True).start()

    def _on_provider_change(self, _event=None):
        """A different translation source was picked: fetch a fresh translation from it."""
        self._start_translate(show_tab=True, refresh=True)

    def _translate_worker(self, word: str, tl: str, blocks: list[Block], provider: str,
                          refresh: bool, token: int, translator: Translator, sl: str):
        try:
            translator.mode = provider
            wt = translator.word(word, tl, refresh, sl)
            translated = translator.blocks(blocks, tl, refresh)
            self.q.put(("translation", word, tl, wt, translated, token, translator.last_provider))
        except Exception as e:
            self.q.put(("tr_err", word, f"Translation failed: {e}", token))

    def _on_translation(self, word: str, tl: str, wt: dict, blocks: list[Block], token: int, used: str):
        if (self.current is None or self.current.word != word or tl != self._target()
                or token != self._tr_token):
            return
        out = [Block("head", f"{word}  →  {wt['main']}", lang=tl, translate=False)]
        for pos, terms in wt.get("alts", []):
            out.append(Block("alt", ", ".join(terms), prefix=f"{pos}:  ", lang=tl, translate=False))
        out += [b for b in blocks if b.kind != "msg"] or []
        self._fill(self.tr_text, out, "t")
        saved = ("saved to the local cache" if offline_flag("do_trans")
                 else "not saved (Offline mode → Translations is unchecked)")
        self._tab_status(f"Translation: “{word}” → {LANG_NAMES.get(tl, tl)} via {used}, {saved}", 1)

    # ------------------------------------------------------------------ speech
    def _speak(self, text: str, lang: str):
        self.status.set(f"🔊 {text[:80]}{'…' if len(text) > 80 else ''}")
        self.speaker.speak(text, lang, self.voice_mode.get())

    def _speak_word(self):
        if self.current:
            self._speak(self.current.word, self.lang)

    def _stop_speech(self):
        self.speaker.stop()
        self.status.set("Speech stopped")

    # ------------------------------------------------------------------ offline packs
    def _bg(self, fn, done):
        """Run fn() in a thread, then call done(result, error) on the UI thread."""
        def run():
            try:
                res, err = fn(), None
            except Exception as e:
                res, err = None, e
            self.q.put(("call", done, res, err))
        threading.Thread(target=run, daemon=True).start()

    def _off_alive(self) -> bool:
        win = getattr(self, "_off_win", None)
        return win is not None and bool(win.winfo_exists())

    def _open_offline(self, code=None, target=None, parent=None):
        """Offline translation packs, any language -> any language. Opened from the Offline mode
        window it is pre-set to that window's data set (source) and target; both can be changed."""
        sl = DATASETS[code].lang if code in DATASETS else self.lang
        langs = sorted(targets_for(""), key=lambda t: t[0].lower())     # every known language, A-Z
        self._off_by_label = dict(langs)
        labels = [t[0] for t in langs]
        src = f"{LANG_NAMES.get(sl, sl)} ({sl})"
        if src not in self._off_by_label:
            src = labels[0]
        tgt = target or self.target_var.get()
        if tgt not in self._off_by_label or tgt == src:
            tgt = default_target(sl)

        if self._off_alive():                      # already open: just point it at the new pair
            self._off_scb.configure(values=labels)
            self._off_tcb.configure(values=labels)
            self._off_svar.set(src)
            self._off_tvar.set(tgt)
            self._off_win.lift()
            return

        self._off_svar = tk.StringVar(value=src)
        self._off_tvar = tk.StringVar(value=tgt)
        win = tk.Toplevel(self)
        self._off_win = win
        win.title("Offline translation packs")
        win.configure(bg=C["bg"])
        win.geometry(fit_geometry(win, self.ui.get("packs_geometry"), "640x520"))
        self._remember_geometry(win, "packs_geometry")
        win.minsize(560, 420)
        win.transient(parent or self)
        outer = ttk.Frame(win, padding=16)
        outer.pack(fill="both", expand=True, padx=10, pady=10)
        outer.columnconfigure(0, weight=1)
        outer.rowconfigure(4, weight=1)
        ttk.Label(outer, text="OFFLINE TRANSLATION", style="Section.TLabel").grid(row=0, column=0, sticky="w")
        ttk.Label(outer, style="Muted.TLabel", wraplength=580, justify="left", text=(
            "Runs on this computer with Argos Translate (pip install argostranslate). Pick any source and "
            "target language; each language needs a one-time download, roughly 50-150 MB per package. "
            "Translations between two non-English languages go through English, so the packages to and "
            "from English are installed as well (they are shared between all pairs). Afterwards choose "
            "“Offline” in the “Translate via” box.")).grid(row=1, column=0, sticky="w", pady=(4, 12))

        top = ttk.Frame(outer)
        top.grid(row=2, column=0, sticky="ew")
        r1 = ttk.Frame(top)
        r1.pack(fill="x")
        ttk.Label(r1, text="From", style="Muted.TLabel").pack(side="left")
        self._off_scb = ttk.Combobox(r1, textvariable=self._off_svar, values=labels,
                                     state="readonly", width=22)
        self._off_scb.pack(side="left", padx=(6, 6))
        ttk.Button(r1, text="⇄", width=3, command=self._offline_swap).pack(side="left")
        ttk.Label(r1, text="To", style="Muted.TLabel").pack(side="left", padx=(12, 6))
        self._off_tcb = ttk.Combobox(r1, textvariable=self._off_tvar, values=labels,
                                     state="readonly", width=22)
        self._off_tcb.pack(side="left")
        r2 = ttk.Frame(top)
        r2.pack(fill="x", pady=(8, 0))
        self._off_dl = ttk.Button(r2, text="2. Download pack", style="Accent.TButton",
                                  command=self._offline_download)
        self._off_dl.pack(side="left")

        ttk.Label(outer, text="INSTALLED PACKAGES", style="Section.TLabel").grid(
            row=3, column=0, sticky="w", pady=(16, 4))
        lf = ttk.Frame(outer)
        lf.grid(row=4, column=0, sticky="nsew")
        lf.rowconfigure(0, weight=1)
        lf.columnconfigure(0, weight=1)
        self._off_list = tk.Listbox(lf, bg=C["input"], fg=C["text"], bd=0, highlightthickness=0,
                                    selectbackground=C["sel"], selectforeground="#ffffff",
                                    font=("Segoe UI", 11), activestyle="none")
        sb = ttk.Scrollbar(lf, orient="vertical", command=self._off_list.yview)
        self._off_list.configure(yscrollcommand=sb.set)
        self._off_list.grid(row=0, column=0, sticky="nsew")
        sb.grid(row=0, column=1, sticky="ns")
        self._off_status = tk.StringVar()
        ttk.Label(outer, textvariable=self._off_status, style="Muted.TLabel", wraplength=580,
                  justify="left").grid(row=5, column=0, sticky="w", pady=(10, 0))
        bf = ttk.Frame(outer)
        bf.grid(row=6, column=0, sticky="ew", pady=(10, 0))
        self._off_eng = ttk.Button(bf, text="1. Install engine", command=self._offline_engine)
        self._off_eng.pack(side="left", padx=(0, 8))
        ttk.Button(bf, text="Remove selected", command=self._offline_remove).pack(side="left")
        ttk.Button(bf, text="Close", command=win.destroy).pack(side="right")
        self._off_pairs: list = []
        self._off_note = ""
        self._offline_refresh()

    def _offline_swap(self):
        s, t = self._off_svar.get(), self._off_tvar.get()
        self._off_svar.set(t)
        self._off_tvar.set(s)

    def _offline_refresh(self):
        ok = offline_available()
        self._off_eng.configure(text="Engine installed ✓" if ok else "1. Install engine")
        self._off_eng.state(["disabled"] if ok else ["!disabled"])
        self._off_dl.state(["!disabled"] if ok else ["disabled"])
        if not ok:
            self._off_list.delete(0, "end")
            self._off_status.set(self._off_note + "The offline engine (argostranslate) is not installed. "
                                 "Click “1. Install engine” (needs internet; it is installed into the lib "
                                 "folder next to the script), then download a language pack.")
            return
        self._off_status.set(self._off_note + "Reading installed packages …")
        self._bg(offline_installed, self._offline_listed)

    def _offline_engine(self):
        self._off_eng.state(["disabled"])
        self._off_dl.state(["disabled"])
        self._off_status.set("Installing engine (this can take a few minutes) …")
        self._bg(lambda: offline_install_engine(APP_DIR / "lib",
                                                lambda m: self.q.put(("call", self._offline_progress, m))),
                 self._offline_engine_done)

    def _offline_engine_done(self, _res, err):
        self._off_note = f"Engine install failed: {err}\n" if err else "Engine installed.  "
        self.status.set(self._off_note.strip().splitlines()[0])
        if self._off_alive():
            self._offline_refresh()

    def _offline_listed(self, pairs, err):
        if not self._off_alive():
            return
        if err:
            self._off_status.set(f"{self._off_note}Could not read packages: {err}")
            return
        self._off_pairs = list(pairs)
        self._off_list.delete(0, "end")
        for a, b in self._off_pairs:
            self._off_list.insert("end", f"{LANG_NAMES.get(a, a)}  →  {LANG_NAMES.get(b, b)}      ({a} → {b})")
        self._off_status.set(f"{self._off_note}{len(pairs)} package(s) installed.")

    def _offline_progress(self, text: str):
        if self._off_alive():
            self._off_status.set(text)
        self.status.set(text)

    def _offline_download(self):
        sl = self._off_by_label.get(self._off_svar.get())
        tl = self._off_by_label.get(self._off_tvar.get())
        if not sl or not tl:
            return
        if sl == tl:
            self._off_status.set("Source and target language must be different.")
            return
        self._off_dl.state(["disabled"])
        self._off_status.set("Looking up packages …")

        def work():
            packages = offline_plan(tl, sl)
            offline_install(packages, lambda m: self.q.put(("call", self._offline_progress, m)))
            return len(packages)

        self._bg(work, self._offline_downloaded)

    def _offline_downloaded(self, n, err):
        if self._off_alive():
            self._off_dl.state(["!disabled"])
        if err:
            self._off_note = f"Download failed: {err}\n"
        elif n == 0:
            self._off_note = "Already installed.  "
        else:
            self._off_note = f"Installed {n} package(s).  "
        self.status.set(self._off_note.strip())
        if self._off_alive():
            self._offline_refresh()

    def _offline_remove(self):
        sel = self._off_list.curselection()
        if not sel:
            return
        pair = self._off_pairs[sel[0]]
        if not messagebox.askyesno("Remove package", f"Delete the {pair[0]} → {pair[1]} package from disk?",
                                   parent=self._off_win):
            return
        self._off_status.set("Removing …")

        def done(_res, err):
            self._off_note = f"Remove failed: {err}\n" if err else f"Removed {pair[0]} → {pair[1]}.  "
            if self._off_alive():
                self._offline_refresh()

        self._bg(lambda: offline_remove(pair), done)

    def _open_offline_mode(self):
        open_offline_mode(self, sys.modules[__name__])

    def _open_translator(self):
        open_translate_window(self, sys.modules[__name__])

    # ------------------------------------------------------------------ coverage estimator
    def _open_coverage(self):
        if not self.entries:
            return
        old = getattr(self, "_cov_win", None)
        if old is not None and old.winfo_exists():
            old.lift()
            return

        entries = self.entries
        N = len(entries)
        cum = list(accumulate(e.freq for e in entries))
        total = cum[-1]

        win = tk.Toplevel(self)
        self._cov_win = win
        win.title("Speech coverage estimator")
        win.configure(bg=C["bg"])
        win.geometry(fit_geometry(win, self.ui.get("cov_geometry"), "600x640"))
        self._remember_geometry(win, "cov_geometry")
        win.minsize(460, 560)
        win.transient(self)
        outer = ttk.Frame(win, padding=16)
        outer.pack(fill="both", expand=True, padx=10, pady=10)
        outer.columnconfigure(0, weight=1)
        outer.rowconfigure(6, weight=1)

        ttk.Label(outer, text="TOP-N WORDS → COVERAGE", style="Section.TLabel").grid(row=0, column=0, sticky="w")
        row1 = ttk.Frame(outer)
        row1.grid(row=1, column=0, sticky="ew", pady=(6, 4))
        ttk.Label(row1, text="If you know the top").pack(side="left")
        n_var = tk.StringVar(value=str(self.ui.get("cov_n", "1000")))
        n_entry = ttk.Entry(row1, textvariable=n_var, width=8, font=("Segoe UI", 11))
        n_entry.pack(side="left", padx=8)
        ttk.Label(row1, text="words").pack(side="left")
        sel_btn = ttk.Button(row1, text="Use selected rank",
                             command=lambda: self.current and n_var.set(str(self.current.rank)))
        sel_btn.pack(side="right")

        result_var = tk.StringVar()
        ttk.Label(outer, textvariable=result_var, style="Big.TLabel").grid(row=2, column=0, sticky="w")
        detail_var = tk.StringVar()
        ttk.Label(outer, textvariable=detail_var, style="Muted.TLabel").grid(row=3, column=0, sticky="w")

        busy = {"v": False}
        scale = ttk.Scale(outer, from_=1, to=N, orient="horizontal")
        scale.grid(row=4, column=0, sticky="ew", pady=(8, 14))

        def on_scale(v):
            if busy["v"]:
                return
            n_var.set(str(int(float(v))))

        scale.configure(command=on_scale)

        def parse_int(s):
            try:
                return int(re.sub(r"[\s,_]", "", s))
            except ValueError:
                return None

        def update(*_):
            n = parse_int(n_var.get())
            ok = n is not None and 1 <= n <= N
            n_entry.configure(style="TEntry" if ok else "Bad.TEntry")
            if not ok:
                result_var.set("—")
                detail_var.set(f"Enter a number from 1 to {N:,}")
                return
            pct = cum[n - 1] / total * 100
            result_var.set(f"{pct:.2f}%")
            last = entries[n - 1]
            detail_var.set(f"of all running text in the list · last word: “{last.word}” "
                           f"(freq {last.freq:,})")
            busy["v"] = True
            scale.set(n)
            busy["v"] = False

        n_var.trace_add("write", update)
        n_var.trace_add("write", lambda *_: self._ui_set("cov_n", n_var.get()))

        # --- reverse: coverage target -> words needed
        ttk.Label(outer, text="COVERAGE TARGET → WORDS NEEDED", style="Section.TLabel").grid(
            row=5, column=0, sticky="w")
        row2 = ttk.Frame(outer)
        row2.grid(row=5, column=0, sticky="ew", pady=(24, 0))
        tgt_var = tk.StringVar(value=str(self.ui.get("cov_target", "90")))
        tgt_entry = ttk.Entry(row2, textvariable=tgt_var, width=7, font=("Segoe UI", 11))
        tgt_var_lbl = tk.StringVar()
        ttk.Label(row2, text="To understand").pack(side="left")
        tgt_entry.pack(side="left", padx=8)
        ttk.Label(row2, text="% of speech you need").pack(side="left")
        ttk.Label(row2, textvariable=tgt_var_lbl, font=FONT_B, foreground=C["accent"]).pack(side="left", padx=8)

        def update_target(*_):
            try:
                t = float(tgt_var.get().replace(",", ".").strip())
            except ValueError:
                t = None
            if t is None or not 0 < t <= 100:
                tgt_entry.configure(style="Bad.TEntry")
                tgt_var_lbl.set("")
                return
            tgt_entry.configure(style="TEntry")
            idx = bisect.bisect_left(cum, t / 100 * total)
            tgt_var_lbl.set(f"~{min(idx + 1, N):,} words")

        tgt_var.trace_add("write", update_target)
        tgt_var.trace_add("write", lambda *_: self._ui_set("cov_target", tgt_var.get()))

        # --- milestones table
        lf = ttk.Frame(outer)
        lf.grid(row=6, column=0, sticky="nsew", pady=(16, 0))
        lf.rowconfigure(0, weight=1)
        lf.columnconfigure(0, weight=1)
        tv = ttk.Treeview(lf, columns=("n", "pct", "flag"), show="headings", height=8)
        for col, text, w, anc in (("n", "Top N words", 140, "e"), ("pct", "Coverage", 120, "e"),
                                  ("flag", "", 10, "w")):
            tv.heading(col, text=text)
            tv.column(col, width=w, anchor=anc, stretch=(col == "flag"))
        tv.tag_configure("even", background=C["card"])
        tv.tag_configure("odd", background=C["stripe"])
        marks = [m for m in (50, 100, 250, 500, 1000, 2000, 3000, 5000, 8000, 10000,
                             15000, 20000, 30000, 40000, 50000) if m < N] + [N]
        for i, m in enumerate(marks):
            tv.insert("", "end", values=(f"{m:,}", f"{cum[m - 1] / total * 100:.2f}%", ""),
                      tags=("odd" if i % 2 else "even",))
        tv.grid(row=0, column=0, sticky="nsew")
        tv.bind("<<TreeviewSelect>>", lambda e: tv.selection() and n_var.set(
            str(parse_int(tv.item(tv.selection()[0], "values")[0]))))

        # --- flagged words (treat flags as "words I know")
        flag_var = tk.StringVar()
        ttk.Label(outer, textvariable=flag_var, style="Muted.TLabel", wraplength=470,
                  justify="left").grid(row=7, column=0, sticky="w", pady=(12, 0))

        def update_flags():
            if not win.winfo_exists():
                return
            fl = self.flags
            ff = sum(e.freq for e in entries if e.word in fl)
            flag_var.set(f"Your flagged words ({len(fl):,}) cover {ff / total * 100:.2f}% of the list's "
                         f"running text.")

        bf = ttk.Frame(outer)
        bf.grid(row=8, column=0, sticky="ew", pady=(10, 0))
        ttk.Button(bf, text="↻  Recount flagged", command=update_flags).pack(side="left")
        ttk.Button(bf, text="Close", command=win.destroy).pack(side="right")
        ttk.Label(outer, style="Muted.TLabel", wraplength=470, justify="left",
                  text=f"Coverage is relative to the {N:,} words in {self.wordlist_path.name} "
                       f"(total {total:,} occurrences), so real-world coverage is slightly lower."
                  ).grid(row=9, column=0, sticky="w", pady=(10, 0))

        update()
        update_target()
        update_flags()

    # ------------------------------------------------------------------ misc
    def _poll_queue(self):
        try:
            while True:
                msg = self.q.get_nowait()
                kind = msg[0]
                if kind == "status":
                    self.status.set(msg[1])
                elif kind == "call":
                    try:
                        msg[1](*msg[2:])
                    except Exception as e:  # a failing callback must not stop the queue polling
                        import traceback
                        traceback.print_exc()
                        self.status.set(f"Internal error: {e}")
                elif kind == "entry":
                    self._on_entry(*msg[1:])
                elif kind == "entry_err":
                    self._inflight.discard(msg[1])
                    if self.current and self.current.word == msg[1]:
                        self._message(self.def_text, msg[2] + "\nPress “Refresh” to retry.")
                        self._tab_status(msg[2], 0, 2)
                elif kind == "translation":
                    self._on_translation(*msg[1:])
                elif kind == "tr_err":
                    if self.current and self.current.word == msg[1] and msg[3] == self._tr_token:
                        self._message(self.tr_text, msg[2])
                        self._tab_status(msg[2], 1)
        except queue.Empty:
            pass
        self.after(80, self._poll_queue)


def main():
    if sys.platform == "win32":  # crisp text on high-DPI screens
        try:
            import ctypes
            ctypes.windll.shcore.SetProcessDpiAwareness(1)
        except Exception:
            pass
        try:  # own taskbar identity so the app icon is shown instead of Python's
            import ctypes
            ctypes.windll.shell32.SetCurrentProcessExplicitAppUserModelID("RuFrequencyDictionary.App")
        except Exception:
            pass
    app = App()
    app.mainloop()


if __name__ == "__main__":
    if len(sys.argv) >= 4 and sys.argv[1] == "--tts-worker":  # child process used for system voices
        sys.exit(tts_worker_main(sys.argv[2], sys.argv[3]))
    main()