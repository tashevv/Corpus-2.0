from __future__ import annotations

import hashlib
import html
import importlib.util
import json
import os
import threading
import time
import urllib.error
import urllib.parse
import urllib.request
from dataclasses import replace
from pathlib import Path

USER_AGENT = "Mozilla/5.0 (X11; Linux x86_64) RuFrequencyDictionary/1.0"

# --------------------------------------------------------------------------- Argos storage location
# Keep Argos' language packs and download cache in a subfolder of the app (data/argos) instead of
# the user profile (C:\Users\<you>\.local\...).  The environment variables must be set before
# argostranslate is imported (it reads them at import time); it is only imported lazily in _argos().
ARGOS_HOME = Path(__file__).resolve().parent / "data" / "argos"
ARGOS_DATA = ARGOS_HOME / "data"
ARGOS_CACHE = ARGOS_HOME / "cache"
ARGOS_PACKAGES = ARGOS_DATA / "argos-translate" / "packages"
ARGOS_DATA.mkdir(parents=True, exist_ok=True)
ARGOS_CACHE.mkdir(parents=True, exist_ok=True)
ARGOS_PACKAGES.mkdir(parents=True, exist_ok=True)

os.environ["XDG_DATA_HOME"] = str(ARGOS_DATA)      # Argos uses <XDG_DATA_HOME>/argos-translate
os.environ["XDG_CACHE_HOME"] = str(ARGOS_CACHE)    # and <XDG_CACHE_HOME>/argos-translate
# Some Argos versions also accept an explicit packages directory; harmless if unused.
os.environ["ARGOS_PACKAGES_DIR"] = str(ARGOS_PACKAGES)
os.environ["ARGOS_TRANSLATE_PACKAGE_DIR"] = str(ARGOS_PACKAGES)


class ProviderError(Exception):
    """A provider could not serve the request; `retry_after` is the suggested cool-down (s)."""

    def __init__(self, msg: str, retry_after: float = 60):
        super().__init__(msg)
        self.retry_after = retry_after


def _http(url: str, data: bytes | None = None, headers: dict | None = None, timeout: float = 20) -> str:
    h = {"User-Agent": USER_AGENT}
    h.update(headers or {})
    req = urllib.request.Request(url, data=data, headers=h)
    try:
        with urllib.request.urlopen(req, timeout=timeout) as resp:
            return resp.read().decode("utf-8", "replace")
    except urllib.error.HTTPError as e:
        wait = 0.0
        try:
            wait = float(e.headers.get("Retry-After", "0"))
        except (TypeError, ValueError):
            pass
        raise ProviderError(f"HTTP {e.code}", wait or (300 if e.code in (403, 429) else 60)) from e
    except (urllib.error.URLError, OSError) as e:  # includes timeouts
        raise ProviderError(f"network error ({e})", 30) from e


def _json(text: str):
    try:
        return json.loads(text)
    except json.JSONDecodeError as e:
        raise ProviderError("invalid JSON in response", 60) from e


# --------------------------------------------------------------------------- providers
class Provider:
    name = ""
    max_chars = 1000     # total characters per request
    max_items = 1        # texts per request

    def available(self) -> bool:
        return True

    def code(self, lang: str) -> str:
        return lang

    def translate_many(self, texts: list[str], tl: str, sl: str) -> list[str]:
        raise NotImplementedError

    def alternatives(self, word: str, tl: str, sl: str = "ru") -> list:
        return []

    def word(self, word: str, tl: str, sl: str = "ru") -> dict:
        main = self.translate_many([word], tl, sl)[0]
        try:
            alts = self.alternatives(word, tl, sl)
        except ProviderError:
            alts = []
        return {"main": main, "alts": alts}


class Google(Provider):
    name = "Google"
    max_chars = 2500
    max_items = 50
    URL = "https://translate.googleapis.com/translate_a/single"

    def _call(self, text: str, tl: str, sl: str, alternatives: bool = False):
        params = [("client", "gtx"), ("sl", sl), ("tl", tl), ("dt", "t"), ("ie", "UTF-8"), ("oe", "UTF-8")]
        if alternatives:
            params.append(("dt", "bd"))
        url = self.URL + "?" + urllib.parse.urlencode(params)
        body = urllib.parse.urlencode({"q": text}).encode("utf-8")
        data = _json(_http(url, body))
        if not isinstance(data, list) or not data or data[0] is None:
            raise ProviderError("unexpected response", 120)
        return data

    @staticmethod
    def _join(data) -> str:
        return "".join(seg[0] for seg in (data[0] or []) if seg and seg[0])

    def translate_many(self, texts, tl, sl):
        texts = [" ".join(t.split()) for t in texts]
        if len(texts) == 1:
            return [self._join(self._call(texts[0], tl, sl))]
        out = self._join(self._call("\n".join(texts), tl, sl)).split("\n")
        if len(out) != len(texts):  # newlines were merged: one by one
            return [self._join(self._call(t, tl, sl)) for t in texts]
        return out

    def word(self, word, tl, sl="ru"):
        data = self._call(word, tl, sl, alternatives=True)
        alts = []
        if len(data) > 1 and data[1]:
            for grp in data[1]:
                if grp and len(grp) > 1:
                    alts.append([grp[0], list(grp[1][:8])])
        return {"main": self._join(data), "alts": alts}


class Microsoft(Provider):
    """Free token endpoint used by Microsoft Edge's built-in page translator."""
    name = "Microsoft"
    max_chars = 8000
    max_items = 100
    AUTH = "https://edge.microsoft.com/translate/auth"
    API = "https://api-edge.cognitive.microsofttranslator.com"
    MAP = {"zh-CN": "zh-Hans", "sr": "sr-Cyrl", "no": "nb", "he": "he"}

    def __init__(self):
        self._token = ""
        self._expires = 0.0
        self._lock = threading.Lock()

    def code(self, lang):
        return self.MAP.get(lang, lang)

    def _auth(self) -> str:
        with self._lock:
            if self._token and time.time() < self._expires:
                return self._token
            tok = _http(self.AUTH).strip()
            if not tok or tok.startswith("{") or len(tok) < 40:
                raise ProviderError("could not obtain a token", 120)
            self._token, self._expires = tok, time.time() + 8 * 60
            return tok

    def _post(self, path: str, query: dict, payload: list):
        url = f"{self.API}{path}?" + urllib.parse.urlencode(query)
        headers = {"Authorization": f"Bearer {self._auth()}", "Content-Type": "application/json"}
        try:
            return _json(_http(url, json.dumps(payload).encode("utf-8"), headers))
        except ProviderError as e:
            if "401" in str(e):  # token expired early
                self._token = ""
            raise

    def translate_many(self, texts, tl, sl):
        q = {"api-version": "3.0", "to": self.code(tl), "textType": "plain"}
        if sl != "auto":
            q["from"] = self.code(sl)
        data = self._post("/translate", q, [{"Text": " ".join(t.split())} for t in texts])
        try:
            return [item["translations"][0]["text"] for item in data]
        except (KeyError, IndexError, TypeError) as e:
            raise ProviderError("unexpected response", 120) from e

    def alternatives(self, word, tl, sl="ru"):
        """Dictionary lookup (only available for some language pairs; failures are ignored)."""
        try:
            data = self._post("/dictionary/lookup",
                              {"api-version": "3.0", "from": self.code(sl), "to": self.code(tl)},
                              [{"Text": word}])
            groups: dict[str, list[str]] = {}
            for tr in data[0].get("translations", []):
                groups.setdefault(str(tr.get("posTag", "")).lower() or "other", []).append(tr["normalizedTarget"])
            return [[pos, terms[:8]] for pos, terms in groups.items()]
        except (ProviderError, KeyError, IndexError, TypeError):
            return []


class MyMemory(Provider):
    name = "MyMemory"
    max_chars = 450       # the API accepts at most 500 bytes per request
    max_items = 1
    URL = "https://api.mymemory.translated.net/get"

    def translate_many(self, texts, tl, sl):
        text = " ".join(texts[0].split())
        params = {"q": text, "langpair": f"{'Autodetect' if sl == 'auto' else sl}|{tl}"}
        email = os.environ.get("MYMEMORY_EMAIL")
        if email:
            params["de"] = email
        data = _json(_http(self.URL + "?" + urllib.parse.urlencode(params)))
        out = (data.get("responseData") or {}).get("translatedText") or ""
        status = str(data.get("responseStatus", "200"))
        if "MYMEMORY WARNING" in out.upper():
            raise ProviderError("daily quota used up", 3600)
        if status == "429":
            raise ProviderError("rate limited", 600)
        if status != "200" or not out:
            raise ProviderError(f"error {status}", 120)
        return [html.unescape(out)]


class Lingva(Provider):
    """Public Lingva mirrors (a Google Translate proxy); tries each mirror in turn."""
    name = "Lingva"
    max_chars = 1200
    max_items = 1
    DEFAULT = ["https://lingva.ml", "https://lingva.thedaviddelta.com", "https://translate.plausibility.cloud"]

    def __init__(self):
        env = os.environ.get("LINGVA_INSTANCES", "")
        self.instances = [u.strip().rstrip("/") for u in env.split(",") if u.strip()] or list(self.DEFAULT)
        self._bad: dict[str, float] = {}

    def code(self, lang):
        return {"zh-CN": "zh"}.get(lang, lang)

    def translate_many(self, texts, tl, sl):
        text = " ".join(texts[0].split())
        last: ProviderError | None = None
        now = time.time()
        order = sorted(self.instances, key=lambda u: self._bad.get(u, 0) > now)  # healthy mirrors first
        for base in order:
            url = f"{base}/api/v1/{self.code(sl)}/{self.code(tl)}/{urllib.parse.quote(text, safe='')}"
            try:
                data = _json(_http(url, timeout=15))
                out = data.get("translation")
                if not out:
                    raise ProviderError("empty translation", 60)
                return [out]
            except ProviderError as e:
                self._bad[base] = time.time() + max(e.retry_after, 60)
                last = e
        raise ProviderError(f"all mirrors failed ({last})", last.retry_after if last else 60)


class LibreTranslate(Provider):
    name = "LibreTranslate"
    max_chars = 3000
    max_items = 40
    MAP = {"zh-CN": "zh", "no": "nb"}

    def available(self):
        return bool(os.environ.get("LIBRETRANSLATE_URL"))

    def code(self, lang):
        return self.MAP.get(lang, lang)

    def translate_many(self, texts, tl, sl):
        base = os.environ["LIBRETRANSLATE_URL"].rstrip("/")
        payload = {"q": [" ".join(t.split()) for t in texts], "source": "auto" if sl == "auto" else self.code(sl),
                   "target": self.code(tl), "format": "text"}
        key = os.environ.get("LIBRETRANSLATE_KEY")
        if key:
            payload["api_key"] = key
        data = _json(_http(base + "/translate", json.dumps(payload).encode("utf-8"),
                           {"Content-Type": "application/json"}, timeout=30))
        out = data.get("translatedText")
        if isinstance(out, str):
            out = [out]
        if not isinstance(out, list):
            raise ProviderError(str(data.get("error", "unexpected response")), 120)
        return out


# --------------------------------------------------------------------------- offline (Argos Translate)
ARGOS_MAP = {"zh-CN": "zh", "no": "nb"}   # app language code -> Argos code


def _argos_pin_paths():
    """Force Argos to use the folders inside the app, whatever the installed version does with env vars."""
    try:
        import argostranslate.settings as st
    except Exception:
        return
    for attr, path in (("package_data_dir", ARGOS_PACKAGES),
                       ("data_dir", ARGOS_DATA / "argos-translate"),
                       ("cache_dir", ARGOS_CACHE / "argos-translate"),
                       ("downloads_dir", ARGOS_CACHE / "argos-translate" / "downloads")):
        if hasattr(st, attr):
            path.mkdir(parents=True, exist_ok=True)
            setattr(st, attr, path)


def _argos():
    try:
        import argostranslate.package as pkg
        import argostranslate.translate as trn
    except Exception as e:   # not only ImportError: broken dependencies fail in other ways
        if isinstance(e, ModuleNotFoundError) and (e.name or "").split(".")[0] == "argostranslate":
            raise ProviderError("the offline engine (argostranslate) is not installed", 3600) from e
        raise ProviderError(f"the offline engine failed to load: {type(e).__name__}: {e}", 3600) from e
    _argos_pin_paths()
    return pkg, trn


def offline_available() -> bool:
    """True when the argostranslate engine is installed (language packs are separate)."""
    return importlib.util.find_spec("argostranslate") is not None


def offline_install_engine(target_dir, progress=None) -> None:
    """pip-install argostranslate into `target_dir` (the app's lib folder, already on sys.path)."""
    import subprocess
    import sys
    if getattr(sys, "frozen", False):
        raise RuntimeError("This is a packaged build; install the engine with:  pip install argostranslate")
    target = Path(target_dir)
    target.mkdir(parents=True, exist_ok=True)
    cmd = [sys.executable, "-m", "pip", "install", "--upgrade", "--disable-pip-version-check",
           "--target", str(target), "argostranslate"]
    kwargs = {"creationflags": 0x08000000} if sys.platform == "win32" else {}
    proc = subprocess.Popen(cmd, stdin=subprocess.DEVNULL, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT, text=True, errors="replace", **kwargs)
    tail: list[str] = []
    for line in proc.stdout:  # type: ignore[union-attr]
        line = line.strip()
        if line:
            tail = (tail + [line])[-8:]
            if progress:
                progress("Installing engine: " + line[:110])
    if proc.wait() != 0:
        raise RuntimeError("pip failed:\n" + "\n".join(tail[-5:]))
    if str(target) not in sys.path:
        sys.path.insert(0, str(target))
    sys.path_importer_cache.pop(str(target), None)
    importlib.invalidate_caches()


def offline_installed() -> list[tuple[str, str]]:
    """Installed language packages as (from_code, to_code) pairs."""
    pkg, _ = _argos()
    return sorted({(p.from_code, p.to_code) for p in pkg.get_installed_packages()})


def offline_plan(tl: str, sl: str = "ru") -> list:
    """Packages still missing to translate from `sl` (and English, for definitions) into `tl`.

    Needs the internet.  Translation between two non-English languages goes through English, so
    sl->en and en->tl are needed; when either side is English only the other package is."""
    pkg, _ = _argos()
    s, t = ARGOS_MAP.get(sl, sl), ARGOS_MAP.get(tl, tl)
    need = ([(s, "en")] if s != "en" else []) + ([("en", t)] if t != "en" else [])
    have = {(p.from_code, p.to_code) for p in pkg.get_installed_packages()}
    missing = [n for n in need if n not in have]
    if not missing:
        return []
    pkg.update_package_index()
    avail = {(p.from_code, p.to_code): p for p in pkg.get_available_packages()}
    out = []
    for n in missing:
        if n not in avail:
            raise RuntimeError(f"No offline package exists for {n[0]} \u2192 {n[1]}.")
        out.append(avail[n])
    return out


def offline_install(packages: list, progress=None) -> None:
    pkg, _ = _argos()
    for i, p in enumerate(packages, 1):
        if progress:
            progress(f"Downloading {p.from_name} \u2192 {p.to_name}  ({i}/{len(packages)}) \u2026")
        pkg.install_from_path(p.download())
    if progress:
        progress("Finishing \u2026")
    Offline.reset()


def offline_remove(pair: tuple[str, str]) -> None:
    pkg, _ = _argos()
    for p in pkg.get_installed_packages():
        if (p.from_code, p.to_code) == tuple(pair):
            pkg.uninstall(p)
    Offline.reset()


class Offline(Provider):
    """Local neural translation with Argos Translate; works without internet."""
    name = "Offline"
    max_chars = 4000
    max_items = 20
    assume_source = "ru"          # used when the source is "auto" (Argos cannot detect languages)
    _tcache: dict = {}

    @classmethod
    def reset(cls):
        """Forget loaded models (call after installing or removing packages)."""
        cls._tcache.clear()
        try:
            import argostranslate.translate as trn
            clear = getattr(trn.get_installed_languages, "cache_clear", None)
            if clear:
                clear()
        except Exception:
            pass

    def available(self) -> bool:
        return offline_available()

    def _steps(self, sl: str, tl: str) -> list:
        a = self.assume_source if sl == "auto" else ARGOS_MAP.get(sl, sl)   # no auto-detection offlineoffline
        b = ARGOS_MAP.get(tl, tl)
        key = (a, b)
        if key in self._tcache:
            return self._tcache[key]
        _, trn = _argos()
        langs = {lang.code: lang for lang in trn.get_installed_languages()}

        def direct(x, y):
            lx, ly = langs.get(x), langs.get(y)
            return lx.get_translation(ly) if lx and ly else None

        steps: list = []
        if a != b:
            t = direct(a, b)
            if t:
                steps = [t]
            elif "en" not in (a, b):
                first, second = direct(a, "en"), direct("en", b)
                if first and second:
                    steps = [first, second]
            if not steps:
                raise ProviderError(
                    f"offline package {a} \u2192 {b} is not installed (use the \u201c\u2b07 Offline packs\u201d button)", 10)
        self._tcache[key] = steps
        return steps

    def translate_many(self, texts, tl, sl):
        steps = self._steps(sl, tl)
        out = []
        try:
            for t in texts:
                t = " ".join(t.split())
                for step in steps:
                    t = step.translate(t)
                out.append(t)
        except Exception as e:
            raise ProviderError(f"offline engine error ({e})", 60) from e
        return out


# --------------------------------------------------------------------------- translator
PROVIDER_CHOICES = ["Auto", "Google", "Microsoft", "Lingva", "MyMemory", "LibreTranslate", "Offline"]


class Translator:
    """Caches in SQLite and fails over between providers.

    `mode` is "Auto" (try providers in order, skipping those on cool-down) or the name of
    one provider.  `last_provider` is the provider that served the most recent request.
    """

    def __init__(self, store):
        self.store = store
        self.mode = "Auto"
        self.last_provider = ""
        self.providers: dict[str, Provider] = {
            p.name: p for p in (Google(), Microsoft(), Lingva(), MyMemory(), LibreTranslate(), Offline())
        }
        self._cool: dict[str, float] = {}

    @staticmethod
    def _key(*parts: str) -> str:
        return hashlib.sha1("|".join(parts).encode("utf-8")).hexdigest()

    # ---- provider selection
    def _chain(self) -> list[Provider]:
        if self.mode in self.providers:
            return [self.providers[self.mode]]
        avail = [p for p in self.providers.values() if p.available()]
        now = time.time()
        ready = [p for p in avail if self._cool.get(p.name, 0) <= now]
        waiting = sorted((p for p in avail if p not in ready), key=lambda p: self._cool[p.name])
        return ready + waiting  # as a last resort even the cooling ones are tried again

    def _chunks(self, p: Provider, texts: list[str]):
        chunk, size = [], 0
        for t in texts:
            if chunk and (len(chunk) >= p.max_items or size + len(t) + 1 > p.max_chars):
                yield chunk
                chunk, size = [], 0
            chunk.append(t)
            size += len(t) + 1
        if chunk:
            yield chunk

    def _run_chain(self, fn):
        errors = []
        for p in self._chain():
            try:
                result = fn(p)
                self.last_provider = p.name
                return result
            except ProviderError as e:
                self._cool[p.name] = time.time() + e.retry_after
                errors.append(f"{p.name}: {e}")
        raise RuntimeError("all translation services failed — " + "; ".join(errors or ["none available"]))

    # ---- public API
    def many(self, texts: list[str], tl: str, sl: str = "auto", refresh: bool = False) -> list[str]:
        texts = [" ".join(t.split()) for t in texts]
        done: dict[str, str] = {}
        todo: list[str] = []
        for t in dict.fromkeys(texts):
            cached = None if refresh else self.store.get_translation(self._key("t", sl, t), tl)
            if cached is not None:
                done[t] = cached
            elif t:
                todo.append(t)
            else:
                done[t] = ""
        if todo:
            def attempt(p: Provider):
                pending = [t for t in todo if t not in done]  # earlier providers may have finished some
                for chunk in self._chunks(p, pending):
                    out = p.translate_many(chunk, tl, sl)
                    if len(out) != len(chunk):
                        raise ProviderError("response did not match the request", 120)
                    for src, dst in zip(chunk, out):
                        done[src] = dst
                        self.store.put_translation(self._key("t", sl, src), tl, dst)
                return True

            self._run_chain(attempt)
        return [done[t] for t in texts]

    def text(self, text: str, tl: str, sl: str = "auto") -> str:
        return self.many([text], tl, sl)[0]

    def word(self, word: str, tl: str, refresh: bool = False, sl: str = "ru") -> dict:
        key = self._key("w", sl, word)
        cached = None if refresh else self.store.get_translation(key, tl)
        if cached is not None:
            return json.loads(cached)
        result = self._run_chain(lambda p: p.word(word, tl, sl))
        self.store.put_translation(key, tl, json.dumps(result, ensure_ascii=False))
        return result

    def blocks(self, blocks: list, tl: str, refresh: bool = False) -> list:
        """Translate every translatable block (batched per source language).
        refresh=True ignores the cache and overwrites it with the new result."""
        out = list(blocks)
        by_lang: dict[str, list[int]] = {}
        for i, b in enumerate(blocks):
            if b.translate and b.text.strip() and b.lang != tl:
                by_lang.setdefault(b.lang, []).append(i)
        for sl, idxs in by_lang.items():
            tr = self.many([blocks[i].text for i in idxs], tl, sl, refresh)
            for i, new in zip(idxs, tr):
                out[i] = replace(blocks[i], text=new.strip(), lang=tl)
        return out