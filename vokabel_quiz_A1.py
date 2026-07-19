#!/usr/bin/env python3
"""
Vokabel-Quiz — Goethe A1 / Start Deutsch 1 vocabulary trainer
=============================================================

Shows an ENGLISH word and you type the GERMAN translation.
Each word comes with a short example sentence: the English version is
shown as a hint, together with the German sentence with the target word
blanked out (_____). The full German sentence appears once you answer.

Buttons:  Check | Show Answer | Prev | Next.  Tag the current word as
Mark, Difficult, or Very difficult, then use the "Practice:" dropdown to
drill All words / Marked / Difficult / Very difficult.  Plus an Example
on/off toggle, a 🔊 pronounce button (Google text-to-speech), skip +/-10,
and Delete word.  All tags and deletions are written back to the .txt file.

This version reads the four-column A1 word-list file
    German  <tab>  English meaning  <tab>  German example  <tab>  English example
(the file "A1_Wortliste_4Spalten.txt" / "A1_Wortliste_Quiz.txt"), with
optional "--- A ---" letter dividers.  A "Markiert" (1/0) and a
"Schwierigkeit" (0/1/2) column are added automatically when you tag a
word, so your marks and difficulty ratings are saved.

It also still reads the older "frequency, German, English, ..." files.

Run it with:
    python vokabel_quiz_A1.py

Requirements: just Python 3 with Tkinter (bundled with the standard
python.org installers on Windows/macOS). On Debian/Ubuntu Linux you may
need:  sudo apt install python3-tk

The 🔊 pronounce button needs an internet connection. It works best with
the small "gTTS" package (pip install gTTS); without it, the app falls
back to calling Google's TTS voice directly. Audio is played with a media
player already on your system (winmm on Windows, afplay on macOS, or
mpg123/ffplay/mpv on Linux), so no extra audio library is required.

The app looks for the vocabulary file next to this script (or in the
current folder). If it can't find one, a file-open dialog appears so you
can point to any tab-separated word file.
"""

import os
import re
import csv
import hashlib
import platform
import shutil
import subprocess
import tempfile
import threading
import tkinter as tk
from tkinter import ttk, filedialog, messagebox

# Files searched for automatically, in order of preference.
DEFAULT_FILENAMES = (
    "A1_Wortliste_Quiz.txt",       # this app's own saved format (with marks)
    "A1_Wortliste_4Spalten.txt",   # the plain 4-column study file
    "Vokabelliste_LiD_Seiten1-12.txt",  # older "Leben in Deutschland" file
)

TRUE_TOKENS = {"1", "*", "x", "true", "yes", "ja", "y"}

# Difficulty tags, stored as a number: 0 = none, 1 = difficult, 2 = very difficult.
DIFF_CODES = {"none": "0", "difficult": "1", "very": "2"}
DIFF_FROM_RAW = {
    "0": "none", "": "none",
    "1": "difficult", "d": "difficult", "difficult": "difficult",
    "2": "very", "vd": "very", "very": "very", "very difficult": "very",
}


def parse_level(raw):
    """Read a stored difficulty value and return 'none' / 'difficult' / 'very'."""
    return DIFF_FROM_RAW.get(str(raw).strip().lower(), "none")


def level_code(level):
    """Turn 'none'/'difficult'/'very' into the number stored in the file."""
    return DIFF_CODES.get(level, "0")


# Practice filter: which subset of words to drill.
PRACTICE_ORDER = ["all", "marked", "difficult", "very"]
PRACTICE_LABELS = {"all": "All words", "marked": "Marked",
                   "difficult": "Difficult", "very": "Very difficult"}
LABEL_TO_MODE = {label: mode for mode, label in PRACTICE_LABELS.items()}

# The A1 file's own header/divider text, reused when saving.
A1_HEADER = ["Deutsches Wort (German)", "Bedeutung (English)",
             "Beispielsatz (German)", "Übersetzung (English)",
             "Markiert (1/0)", "Schwierigkeit (0/1/2)"]
LID_HEADER = ["Häufigkeit", "Deutsch", "Englisch",
              "Markiert", "Beispiel", "Beispiel_Englisch"]


# --------------------------------------------------------------------------
# Small text helpers
# --------------------------------------------------------------------------
def _strip_leading_article(word):
    """Return the word without a leading der/die/das (so 'die Abfahrt' -> 'Abfahrt')."""
    w = word.strip()
    low = w.lower()
    for art in ("der ", "die ", "das "):
        if low.startswith(art):
            return w[len(art):].strip()
    return w


def section_letter(de):
    """First alphabetical letter of the word (ignoring an article), for A/B/C dividers."""
    s = _strip_leading_article(de)
    for ch in s:
        if ch.isalpha():
            u = ch.upper()
            return {"Ä": "A", "Ö": "O", "Ü": "U"}.get(u, u)
    return "#"


def _looks_like_header(de, en):
    """True if a row is clearly the column-title row rather than a real word."""
    d, e = de.lower(), en.lower()
    de_h = any(k in d for k in ("deutsch", "german", "wort"))
    en_h = any(k in e for k in ("english", "englisch", "bedeutung", "meaning"))
    return de_h and en_h


def normalize(text):
    """
    Normalise a German string for lenient comparison:
    - lowercase, trimmed
    - umlaut/ß equivalence (ä=ae, ö=oe, ü=ue, ß=ss) so 'Bürger' == 'Buerger'
    - collapse internal whitespace
    """
    text = text.strip().lower()
    for a, b in (("ä", "ae"), ("ö", "oe"), ("ü", "ue"), ("ß", "ss")):
        text = text.replace(a, b)
    text = " ".join(text.split())
    return text


def answer_matches(user, correct_de):
    """
    Accept the answer if it matches the German word, with or without its
    article — so both 'die Abfahrt' and 'Abfahrt' are counted correct.
    """
    nu = normalize(user)
    if nu == normalize(correct_de):
        return True
    stripped = _strip_leading_article(correct_de)
    if stripped != correct_de and nu == normalize(stripped):
        return True
    return False


# German letters that must not count as a word boundary.
_LETTER = r"[^\W\d_]"


def mask_word(sentence, word, blank="_____"):
    """
    Hide `word` in `sentence` (case-insensitively, whole words only) so the
    example can be shown as a hint without giving the answer away, e.g.
        mask_word("Vor der Abfahrt rufe ich an.", "die Abfahrt")
        -> "Vor der _____ rufe ich an."
    Also tries the word without its article, so article-nouns still hint.
    Returns "" (meaning "no safe hint") if the word only appears inside a
    longer compound.
    """
    if not sentence or not word:
        return sentence
    candidates = [word]
    stripped = _strip_leading_article(word)
    if stripped and stripped != word:
        candidates.append(stripped)

    for cand in candidates:
        pattern = re.compile(
            rf"(?<!{_LETTER}){re.escape(cand)}(?!{_LETTER})",
            re.IGNORECASE | re.UNICODE,
        )
        masked, n = pattern.subn(blank, sentence)
        if n:
            return masked

    # The word is only present inside a longer compound (e.g. "Bund" in
    # "Bundestag") — showing that would give the answer away.
    for cand in candidates:
        if re.search(re.escape(cand), sentence, re.IGNORECASE):
            return ""
    return sentence


# --------------------------------------------------------------------------
# Loading / saving the vocabulary file
# --------------------------------------------------------------------------
def find_vocab_file():
    """Return a path to the vocab file, or None if it must be chosen manually."""
    here = os.path.dirname(os.path.abspath(__file__))
    for name in DEFAULT_FILENAMES:
        for base in (here, os.getcwd()):
            path = os.path.join(base, name)
            if os.path.isfile(path):
                return path
    return None


def _field(row, i):
    return row[i].strip() if len(row) > i else ""


def _load_lid(rows):
    """Old format: frequency, German, English, marked, ex_de, ex_en."""
    entries, header = [], None
    for row in rows:
        if len(row) < 3:
            continue
        freq, de, en = row[0].strip(), row[1].strip(), row[2].strip()
        marked = _field(row, 3).lower() in TRUE_TOKENS
        if not freq.isdigit():                 # header / non-data row
            if header is None and de and en:
                header = tuple(c.strip() for c in row)
            continue
        if not de or not en:
            continue
        entries.append({"freq": freq, "de": de, "en": en, "marked": marked,
                        "ex_de": _field(row, 4), "ex_en": _field(row, 5),
                        "level": parse_level(_field(row, 6)),
                        "sec": None})
    return entries, header, "lid", False


def _load_a1(rows):
    """New format: German, English, ex_de, ex_en, [marked], with --- X --- dividers."""
    entries, header, current_section = [], None, None
    has_dividers = False
    for row in rows:
        c0 = _field(row, 0)
        if not c0:
            continue
        if c0.startswith("---"):               # letter divider, e.g. "--- A ---"
            m = re.match(r"-+\s*(.+?)\s*-+$", c0)
            if m:
                current_section = m.group(1).strip().upper()
                has_dividers = True
            continue
        de = c0
        en = _field(row, 1)
        if header is None and _looks_like_header(de, en):
            header = tuple(c.strip() for c in row)
            continue
        if not de or not en:
            continue
        entries.append({"de": de, "en": en,
                        "ex_de": _field(row, 2), "ex_en": _field(row, 3),
                        "marked": _field(row, 4).lower() in TRUE_TOKENS,
                        "level": parse_level(_field(row, 5)),
                        "sec": current_section})
    return entries, header, "a1", has_dividers


def load_vocab(path):
    """
    Load a tab-separated vocabulary file. Auto-detects the format:
      * if any row's first column is a number -> old "frequency-first" file
      * otherwise -> the A1 "German-first" file
    Returns (entries, header, fmt, has_dividers).
    """
    rows = []
    with open(path, encoding="utf-8") as f:
        for row in csv.reader(f, delimiter="\t"):
            rows.append(row)

    fmt = "a1"
    for row in rows:
        if row and row[0].strip().isdigit():
            fmt = "lid"
            break
    return _load_lid(rows) if fmt == "lid" else _load_a1(rows)


def save_vocab(path, entries, header, fmt, use_dividers=True):
    """
    Rewrite the whole file from `entries`.
      * a1  -> German, English, ex_de, ex_en, marked  (+ regenerated dividers)
      * lid -> frequency, German, English, marked, ex_de, ex_en
    Returns True on success, False on write error.
    """
    try:
        if fmt == "lid":
            base_h = LID_HEADER + ["Schwierigkeit (0/1/2)"]
            h = list(header or [])[:7]
            h += base_h[len(h):]
            with open(path, "w", encoding="utf-8", newline="") as f:
                w = csv.writer(f, delimiter="\t", lineterminator="\n")
                w.writerow(h)
                for e in entries:
                    w.writerow([e.get("freq", ""), e["de"], e["en"],
                                "1" if e["marked"] else "0",
                                e.get("ex_de", ""), e.get("ex_en", ""),
                                level_code(e.get("level", "none"))])
            return True

        # a1 format
        h = list(header or [])[:6]
        h += A1_HEADER[len(h):]
        with open(path, "w", encoding="utf-8", newline="") as f:
            w = csv.writer(f, delimiter="\t", lineterminator="\n")
            w.writerow(h)
            cur = None
            for e in entries:
                if use_dividers:
                    sec = e.get("sec") or section_letter(e["de"])
                    if sec != cur:
                        cur = sec
                        w.writerow([f"--- {sec} ---"])
                w.writerow([e["de"], e["en"], e.get("ex_de", ""),
                            e.get("ex_en", ""), "1" if e["marked"] else "0",
                            level_code(e.get("level", "none"))])
        return True
    except OSError:
        return False


# --------------------------------------------------------------------------
# Pronunciation (Google Translate text-to-speech)
# --------------------------------------------------------------------------
# German audio is fetched from Google's free Translate TTS voice and cached
# as small MP3 files, so each word is only downloaded once. Playback uses a
# player already on your system, so no extra audio library is required:
#   Windows -> the built-in Media Control Interface (winmm)
#   macOS   -> the built-in "afplay" command
#   Linux   -> mpg123 / ffplay / mpv / cvlc, whichever is installed
# Fetching needs internet; the "gtts" package is used if installed
# (pip install gTTS), otherwise the endpoint is called directly.
CACHE_DIR = os.path.join(tempfile.gettempdir(), "vokabel_tts")
_AUDIO_LOCK = threading.Lock()


def _fetch_tts_mp3(text, lang="de"):
    """Return a path to an MP3 of `text` spoken in `lang`, or None on failure."""
    if not text.strip():
        return None
    key = hashlib.md5(f"{lang}:{text}".encode("utf-8")).hexdigest()
    path = os.path.join(CACHE_DIR, key + ".mp3")
    if os.path.isfile(path) and os.path.getsize(path) > 0:
        return path                       # already downloaded before
    try:
        os.makedirs(CACHE_DIR, exist_ok=True)
    except OSError:
        return None

    # Preferred: the gTTS package (handles headers, chunking, escaping).
    try:
        from gtts import gTTS
        gTTS(text=text, lang=lang).save(path)
        if os.path.getsize(path) > 0:
            return path
    except Exception:
        pass

    # Fallback: call the free Google Translate TTS endpoint directly.
    try:
        import urllib.parse
        import urllib.request
        url = ("https://translate.google.com/translate_tts?ie=UTF-8"
               f"&client=tw-ob&tl={lang}&q=" + urllib.parse.quote(text))
        req = urllib.request.Request(url, headers={"User-Agent": "Mozilla/5.0"})
        data = urllib.request.urlopen(req, timeout=8).read()
        with open(path, "wb") as f:
            f.write(data)
        if os.path.getsize(path) > 0:
            return path
    except Exception:
        pass

    # Clean up an empty/partial file so we retry cleanly next time.
    try:
        if os.path.isfile(path) and os.path.getsize(path) == 0:
            os.remove(path)
    except OSError:
        pass
    return None


def _play_audio(path):
    """Play an MP3 file using whatever player the OS provides. Returns True/False."""
    system = platform.system()
    try:
        if system == "Windows":
            import ctypes
            alias = "vokabel_snd"
            mci = ctypes.windll.winmm.mciSendStringW
            mci(f"close {alias}", None, 0, None)             # close a leftover, if any
            if mci(f'open "{path}" type mpegvideo alias {alias}', None, 0, None) != 0:
                # some systems prefer no explicit type
                if mci(f'open "{path}" alias {alias}', None, 0, None) != 0:
                    return False
            mci(f"play {alias} wait", None, 0, None)
            mci(f"close {alias}", None, 0, None)
            return True
        if system == "Darwin":
            if shutil.which("afplay"):
                subprocess.run(["afplay", path], check=False)
                return True
            return False
        # Linux and other Unixes: try common command-line players.
        players = (
            ["mpg123", "-q"],
            ["ffplay", "-nodisp", "-autoexit", "-loglevel", "quiet"],
            ["mpv", "--no-video", "--really-quiet"],
            ["cvlc", "--play-and-exit", "--quiet"],
        )
        for player in players:
            if shutil.which(player[0]):
                subprocess.run(player + [path], check=False)
                return True
        return False
    except Exception:
        return False


def speak(text, lang="de"):
    """Fetch (or reuse) and play the pronunciation of `text`. Returns True/False."""
    with _AUDIO_LOCK:
        path = _fetch_tts_mp3(text, lang)
        if not path:
            return False
        return _play_audio(path)


# --------------------------------------------------------------------------
# The quiz application
# --------------------------------------------------------------------------
class VokabelQuiz(tk.Tk):
    def __init__(self, entries, path=None, header=None, fmt="a1", use_dividers=True):
        super().__init__()
        self.title("Vokabel-Quiz — Goethe A1 / Start Deutsch 1")
        self.geometry("660x580")
        self.minsize(600, 540)
        self.configure(bg="#f4f6f8")

        self.path = path        # source .txt file (needed for Delete / Mark)
        self.header = header    # original header tuple, or None
        self.fmt = fmt          # "a1" or "lid"
        self.use_dividers = use_dividers  # keep A/B/C dividers only if the file had them
        self.entries = entries
        self.practice_mode = "all"  # all / marked / difficult / very
        self.show_examples = True  # show the example sentence as a hint
        self.pos = 0
        self.answered = False   # True once Check or Show Answer has been used
        self.correct = 0
        self.attempted = 0

        self._build_ui()
        self.rebuild_order()
        self._show_current()

    def rebuild_order(self):
        """Rebuild the practice sequence for the current filter and reset to start."""
        self.order = [i for i, e in enumerate(self.entries) if self._in_mode(e)]
        self.pos = 0

    def _in_mode(self, e, mode=None):
        """True if entry `e` belongs to the given practice filter."""
        mode = mode or self.practice_mode
        if mode == "marked":
            return e["marked"]
        if mode == "difficult":
            return e.get("level") == "difficult"
        if mode == "very":
            return e.get("level") == "very"
        return True

    # ---- UI construction -------------------------------------------------
    def _build_ui(self):
        pad = {"padx": 18, "pady": 6}

        # Top status bar: progress (left) and score (right)
        status = tk.Frame(self, bg="#f4f6f8")
        status.pack(fill="x", **pad)
        self.progress_lbl = tk.Label(
            status, text="", bg="#f4f6f8", fg="#555", font=("Segoe UI", 10)
        )
        self.progress_lbl.pack(side="left")
        self.score_lbl = tk.Label(
            status, text="", bg="#f4f6f8", fg="#555", font=("Segoe UI", 10)
        )
        self.score_lbl.pack(side="right")

        # Prompt card: the English word to translate
        card = tk.Frame(self, bg="white", bd=0, highlightthickness=1,
                        highlightbackground="#d9dee3")
        card.pack(fill="x", padx=18, pady=(4, 10))
        tk.Label(card, text="Translate into German:", bg="white", fg="#8a949e",
                 font=("Segoe UI", 10)).pack(anchor="w", padx=16, pady=(12, 0))
        self.prompt_lbl = tk.Label(
            card, text="", bg="white", fg="#1f2d3d",
            font=("Segoe UI", 20, "bold"), wraplength=540, justify="left"
        )
        self.prompt_lbl.pack(anchor="w", padx=16, pady=(2, 6))
        self.freq_lbl = tk.Label(card, text="", bg="white", fg="#aab2ba",
                                 font=("Segoe UI", 9))
        self.freq_lbl.pack(anchor="w", padx=16, pady=(0, 4))

        # Example sentence: English gloss + German sentence with the word
        # blanked out until the answer is revealed.
        tk.Frame(card, bg="#eef1f4", height=1).pack(fill="x", padx=16, pady=(2, 8))
        self.ex_en_lbl = tk.Label(card, text="", bg="white", fg="#8a949e",
                                  font=("Segoe UI", 10, "italic"),
                                  wraplength=560, justify="left")
        self.ex_en_lbl.pack(anchor="w", padx=16)
        self.ex_de_lbl = tk.Label(card, text="", bg="white", fg="#5b6570",
                                  font=("Segoe UI", 12), wraplength=560,
                                  justify="left")
        self.ex_de_lbl.pack(anchor="w", padx=16, pady=(2, 6))

        self.mark_lbl = tk.Label(card, text="", bg="white", fg="#e0a400",
                                 font=("Segoe UI", 10, "bold"))
        self.mark_lbl.pack(anchor="w", padx=16, pady=(0, 12))

        # Answer entry
        self.answer_var = tk.StringVar()
        self.entry = tk.Entry(self, textvariable=self.answer_var,
                              font=("Segoe UI", 16), justify="center", relief="flat",
                              highlightthickness=2, highlightbackground="#c3ccd4",
                              highlightcolor="#3b82f6")
        self.entry.pack(fill="x", padx=18, ipady=8, pady=(2, 4))
        self.entry.bind("<Return>", self._on_enter)
        self.entry.focus_set()

        # Feedback line
        self.feedback_lbl = tk.Label(self, text="", bg="#f4f6f8",
                                     font=("Segoe UI", 12), wraplength=560,
                                     justify="center")
        self.feedback_lbl.pack(fill="x", padx=18, pady=(6, 4))

        # Study controls — row 0: tag the current word; row 1: pick what to practise
        study = tk.Frame(self, bg="#f4f6f8")
        study.pack(pady=(2, 2))
        self.mark_btn = tk.Button(study, text="☆  Mark", width=11,
                                  command=self.toggle_mark,
                                  bg="#fff4d6", fg="#8a6d00", relief="flat",
                                  font=("Segoe UI", 11, "bold"),
                                  activebackground="#ffe9a8", cursor="hand2")
        self.mark_btn.grid(row=0, column=0, padx=5, pady=(0, 4), ipady=3)
        self.diff_btn = tk.Button(study, text="◆  Difficult", width=12,
                                  command=lambda: self.set_difficulty("difficult"),
                                  bg="#ffe3c2", fg="#8a4b00", relief="flat",
                                  font=("Segoe UI", 11, "bold"),
                                  activebackground="#ffd39e", cursor="hand2")
        self.diff_btn.grid(row=0, column=1, padx=5, pady=(0, 4), ipady=3)
        self.vdiff_btn = tk.Button(study, text="◆◆  Very difficult", width=16,
                                   command=lambda: self.set_difficulty("very"),
                                   bg="#ffd0d0", fg="#8a0000", relief="flat",
                                   font=("Segoe UI", 11, "bold"),
                                   activebackground="#ffb8b8", cursor="hand2")
        self.vdiff_btn.grid(row=0, column=2, padx=5, pady=(0, 4), ipady=3)
        self.speak_btn = tk.Button(study, text="🔊  Say", width=8,
                                   command=self.pronounce,
                                   bg="#e7f0ff", fg="#1f4e9b", relief="flat",
                                   font=("Segoe UI", 11, "bold"),
                                   activebackground="#d6e6ff", cursor="hand2")
        self.speak_btn.grid(row=0, column=3, padx=5, pady=(0, 4), ipady=3)

        tk.Label(study, text="Practice:", bg="#f4f6f8", fg="#555",
                 font=("Segoe UI", 11)).grid(row=1, column=0, sticky="e", padx=(0, 4))
        self.mode_var = tk.StringVar(value=PRACTICE_LABELS["all"])
        self.mode_combo = ttk.Combobox(
            study, textvariable=self.mode_var, state="readonly", width=15,
            values=[PRACTICE_LABELS[m] for m in PRACTICE_ORDER],
            font=("Segoe UI", 11))
        self.mode_combo.grid(row=1, column=1, padx=5, pady=(2, 0), sticky="w")
        self.mode_combo.bind("<<ComboboxSelected>>", self.on_mode_select)
        self.ex_btn = tk.Button(study, text="💡  Example: on", width=16,
                                command=self.toggle_examples,
                                bg="#e5e9ee", fg="#1f2d3d", relief="flat",
                                font=("Segoe UI", 11), cursor="hand2")
        self.ex_btn.grid(row=1, column=2, columnspan=2, padx=5, pady=(2, 0), ipady=2)

        # Buttons
        btns = tk.Frame(self, bg="#f4f6f8")
        btns.pack(pady=8)
        self.prev_btn = tk.Button(btns, text="←  Prev", width=10,
                                  command=self.prev_word,
                                  bg="#e5e9ee", fg="#1f2d3d", relief="flat",
                                  font=("Segoe UI", 11), cursor="hand2")
        self.prev_btn.grid(row=0, column=0, padx=6, ipady=4)
        self.check_btn = tk.Button(btns, text="Check", width=10,
                                   command=self.check_answer,
                                   bg="#3b82f6", fg="white", relief="flat",
                                   font=("Segoe UI", 11, "bold"),
                                   activebackground="#2f6fe0", cursor="hand2")
        self.check_btn.grid(row=0, column=1, padx=6, ipady=4)
        self.show_btn = tk.Button(btns, text="Show Answer", width=10,
                                  command=self.show_answer,
                                  bg="#e5e9ee", fg="#1f2d3d", relief="flat",
                                  font=("Segoe UI", 11), cursor="hand2")
        self.show_btn.grid(row=0, column=2, padx=6, ipady=4)
        self.next_btn = tk.Button(btns, text="Next  →", width=10,
                                  command=self.next_word,
                                  bg="#e5e9ee", fg="#1f2d3d", relief="flat",
                                  font=("Segoe UI", 11), cursor="hand2")
        self.next_btn.grid(row=0, column=3, padx=6, ipady=4)

        # Footer: skip +/-10 and restart
        footer = tk.Frame(self, bg="#f4f6f8")
        footer.pack(pady=(4, 8))
        link_style = dict(bg="#f4f6f8", fg="#3b82f6", relief="flat",
                          font=("Segoe UI", 9, "underline"), cursor="hand2",
                          activebackground="#f4f6f8")
        self.back10_btn = tk.Button(footer, text="«  −10",
                                    command=lambda: self.jump(-10), **link_style)
        self.back10_btn.pack(side="left", padx=10)
        tk.Button(footer, text="Restart (from beginning)",
                  command=self.restart, **link_style).pack(side="left", padx=10)
        self.skip10_btn = tk.Button(footer, text="+10  »",
                                    command=lambda: self.jump(10), **link_style)
        self.skip10_btn.pack(side="left", padx=10)

        # Destructive action kept apart from navigation, on the right
        self.delete_btn = tk.Button(
            footer, text="🗑  Delete word", command=self.delete_word,
            bg="#f4f6f8", fg="#d64545", relief="flat",
            font=("Segoe UI", 9, "underline"), cursor="hand2",
            activebackground="#f4f6f8", activeforeground="#b53030")
        self.delete_btn.pack(side="right", padx=10)

        # Keyboard shortcuts: Ctrl+N next, Ctrl+P previous, PageDown/PageUp +/-10
        self.bind("<Control-n>", lambda e: self.next_word())
        self.bind("<Control-p>", lambda e: self.prev_word())
        self.bind("<Next>", lambda e: self.jump(10))     # PageDown
        self.bind("<Prior>", lambda e: self.jump(-10))   # PageUp
        self.bind("<Control-m>", lambda e: self.toggle_mark())
        self.bind("<Control-d>", lambda e: self.set_difficulty("difficult"))
        self.bind("<Control-e>", lambda e: self.toggle_examples())
        self.bind("<Control-s>", lambda e: self.pronounce())

    # ---- Quiz logic ------------------------------------------------------
    def _current(self):
        return self.entries[self.order[self.pos]]

    def _show_current(self):
        item = self._current()
        self.answered = False
        self.answer_var.set("")
        self.entry.config(state="normal")
        self.entry.focus_set()
        self.prompt_lbl.config(text=item["en"])
        if self.fmt == "lid" and item.get("freq"):
            self.freq_lbl.config(text=f"frequency in test catalogue: {item['freq']}×")
        else:
            self.freq_lbl.config(text="")
        self.feedback_lbl.config(text="", fg="#555")
        self.progress_lbl.config(
            text=f"Word {self.pos + 1} / {len(self.order)}"
        )
        self.prev_btn.config(state="normal" if self.pos > 0 else "disabled")
        self.back10_btn.config(state="normal" if self.pos > 0 else "disabled")
        self.skip10_btn.config(
            state="normal" if self.pos < len(self.order) - 1 else "disabled")
        self._update_example()
        self._update_tag_ui()
        self._update_score()

    # ---- Example sentence ------------------------------------------------
    def _update_example(self):
        """
        Show the example for the current word: before answering, the German
        sentence has the target word blanked out (and only if hints are on);
        after answering, the full sentence is revealed.
        """
        item = self._current()
        ex_de, ex_en = item.get("ex_de", ""), item.get("ex_en", "")
        if not ex_de and not ex_en:
            self.ex_en_lbl.config(text="")
            self.ex_de_lbl.config(text="— no example for this word —",
                                  fg="#c3ccd4")
            return
        if self.answered:
            self.ex_en_lbl.config(text=ex_en)
            self.ex_de_lbl.config(text=ex_de, fg="#1f9d55")
            return
        if not self.show_examples:
            self.ex_en_lbl.config(text="")
            self.ex_de_lbl.config(text="(example hidden — Ctrl+E)", fg="#c3ccd4")
            return
        hint = mask_word(ex_de, item["de"])
        self.ex_en_lbl.config(text=ex_en)
        self.ex_de_lbl.config(text=hint or "(hint hidden for this word)",
                              fg="#5b6570" if hint else "#c3ccd4")

    def toggle_examples(self):
        """Turn the example hint on or off (it is always shown after answering)."""
        self.show_examples = not self.show_examples
        self.ex_btn.config(
            text="💡  Example: on" if self.show_examples else "💡  Example: off"
        )
        self._update_example()

    def pronounce(self):
        """Speak the current German word aloud (fetched from Google TTS)."""
        if not self.order:
            return
        text = self._current()["de"]
        self.speak_btn.config(text="🔊  …", state="disabled")

        def worker():
            ok = speak(text)

            def done():
                self.speak_btn.config(text="🔊  Say", state="normal")
                if not ok:
                    self.feedback_lbl.config(
                        text="Couldn't play audio — check your internet "
                             "connection (and try: pip install gTTS).",
                        fg="#d64545")
            try:
                self.after(0, done)
            except Exception:
                pass

        threading.Thread(target=worker, daemon=True).start()

    def _update_score(self):
        self.score_lbl.config(
            text=f"Score: {self.correct} / {self.attempted}"
        )

    def check_answer(self):
        if self.answered:
            # already scored this word — treat Check as Next for convenience
            self.next_word()
            return
        user = self.answer_var.get()
        if not user.strip():
            self.feedback_lbl.config(text="Type your answer first, "
                                          "or press “Show Answer”.", fg="#8a949e")
            return
        correct_de = self._current()["de"]
        self.attempted += 1
        self.answered = True
        if answer_matches(user, correct_de):
            self.correct += 1
            self.feedback_lbl.config(text=f"✓  Correct!  →  {correct_de}",
                                     fg="#1f9d55")
        else:
            self.feedback_lbl.config(
                text=f"✗  Not quite.  Correct answer:  {correct_de}",
                fg="#d64545"
            )
        self.entry.config(state="disabled")
        self._update_example()
        self._update_score()

    def show_answer(self):
        if not self.answered:
            # revealing without a guess counts as an attempt, not a point
            self.attempted += 1
            self.answered = True
            self._update_score()
        correct_de = self._current()["de"]
        self.feedback_lbl.config(text=f"Answer:  {correct_de}", fg="#3b82f6")
        self.entry.config(state="disabled")
        self._update_example()

    def next_word(self):
        if self.pos + 1 >= len(self.order):
            self._finish()
            return
        self.pos += 1
        self._show_current()

    def prev_word(self):
        if self.pos == 0:
            return
        self.pos -= 1
        self._show_current()

    def jump(self, delta):
        """Skip forward/backward by `delta` words, clamped to the list ends."""
        new_pos = max(0, min(self.pos + delta, len(self.order) - 1))
        if new_pos != self.pos:
            self.pos = new_pos
            self._show_current()

    # ---- Persistence -----------------------------------------------------
    def save_file(self):
        """Rewrite the whole .txt file from self.entries. Returns True on success."""
        if not self.path:
            return False
        return save_vocab(self.path, self.entries, self.header, self.fmt, self.use_dividers)

    # ---- Mark / difficulty / practice-filter -----------------------------
    def toggle_mark(self):
        """Mark or unmark the current word and persist it to the file."""
        if not self.order:
            return
        item = self._current()
        item["marked"] = not item["marked"]
        if self.path and not self.save_file():
            item["marked"] = not item["marked"]   # revert on write failure
            messagebox.showwarning(
                "Not saved", "Couldn't write the file — the change was not saved."
            )
            return
        self._update_tag_ui()

    def set_difficulty(self, target):
        """Tag the current word 'difficult' or 'very' (click the same one to clear)."""
        if not self.order:
            return
        item = self._current()
        old = item.get("level", "none")
        item["level"] = "none" if old == target else target
        if self.path and not self.save_file():
            item["level"] = old                   # revert on write failure
            messagebox.showwarning(
                "Not saved", "Couldn't write the file — the change was not saved."
            )
            return
        self._update_tag_ui()

    def _update_tag_ui(self):
        """Sync the indicator line and the tag buttons to the current word."""
        if not self.order:
            self.mark_lbl.config(text="")
            return
        item = self._current()
        marked = item["marked"]
        level = item.get("level", "none")

        parts = []
        if marked:
            parts.append("★ marked")
        if level == "difficult":
            parts.append("◆ difficult")
        elif level == "very":
            parts.append("◆◆ very difficult")
        self.mark_lbl.config(text="     ".join(parts))

        self.mark_btn.config(text="★  Unmark" if marked else "☆  Mark")
        self.diff_btn.config(relief="sunken" if level == "difficult" else "flat")
        self.vdiff_btn.config(relief="sunken" if level == "very" else "flat")

    def on_mode_select(self, event=None):
        """The practice dropdown changed — rebuild the set of words to drill."""
        mode = LABEL_TO_MODE.get(self.mode_var.get(), "all")
        if mode == self.practice_mode:
            return
        if mode != "all" and not any(self._in_mode(e, mode) for e in self.entries):
            messagebox.showinfo(
                "Nothing to practise yet",
                f"You haven't tagged any words as “{PRACTICE_LABELS[mode]}” yet.\n"
                "Tag some words first, then choose this again."
            )
            self.mode_var.set(PRACTICE_LABELS[self.practice_mode])   # revert display
            return
        self.practice_mode = mode
        self.rebuild_order()
        self.correct = self.attempted = 0
        self._show_current()

    # ---- Delete ----------------------------------------------------------
    def delete_word(self):
        """Permanently remove the current word from memory and the .txt file."""
        if not self.order:
            return
        idx = self.order[self.pos]          # index into self.entries
        item = self.entries[idx]

        if not messagebox.askyesno(
            "Delete word",
            "Permanently delete this word from the file?\n\n"
            f"    {item['de']}  —  {item['en']}\n\n"
            "This cannot be undone."
        ):
            return

        # Snapshot so we can roll back if the file write fails.
        snap_entries, snap_order, snap_pos = (
            list(self.entries), list(self.order), self.pos
        )
        del self.entries[idx]
        self.order = [j - 1 if j > idx else j for j in self.order if j != idx]

        if self.path and not self.save_file():
            self.entries, self.order, self.pos = snap_entries, snap_order, snap_pos
            messagebox.showwarning(
                "Not deleted", "Couldn't write the file — nothing was changed."
            )
            return

        if not self.order:
            if self.entries and self.practice_mode != "all":
                messagebox.showinfo(
                    "Practice set empty",
                    "That was the last word in this set. Switching to all words."
                )
                self.practice_mode = "all"
                self.mode_var.set(PRACTICE_LABELS["all"])
                self.rebuild_order()
                self._show_current()
            else:
                messagebox.showinfo("Empty", "That was the last word. Closing.")
                self.destroy()
            return

        # Staying at the same position now shows what was the next word.
        if self.pos >= len(self.order):
            self.pos = len(self.order) - 1
        self._show_current()

    def _on_enter(self, _event):
        # Enter checks the answer; if already answered, Enter goes to next word
        if self.answered:
            self.next_word()
        else:
            self.check_answer()

    def restart(self):
        self.rebuild_order()
        self.correct = 0
        self.attempted = 0
        self._show_current()

    def _finish(self):
        pct = (self.correct / self.attempted * 100) if self.attempted else 0
        messagebox.showinfo(
            "Done!",
            f"You reached the end of the list.\n\n"
            f"Score: {self.correct} / {self.attempted}  ({pct:.0f}%)\n\n"
            f"Click OK, then “Restart (from beginning)” to go again."
        )


# --------------------------------------------------------------------------
def main():
    path = find_vocab_file()
    if path is None:
        # Ask the user to locate the file
        root = tk.Tk()
        root.withdraw()
        path = filedialog.askopenfilename(
            title="Select the vocabulary file (tab-separated .txt)",
            filetypes=[("Text files", "*.txt"), ("All files", "*.*")],
        )
        root.destroy()
        if not path:
            print("No file selected — exiting.")
            return

    entries, header, fmt, use_dividers = load_vocab(path)
    if not entries:
        messagebox.showerror(
            "No vocabulary found",
            "The file was opened but no valid rows were found.\n"
            "Expected a tab-separated file with German and English columns."
        )
        return

    app = VokabelQuiz(entries, path, header, fmt, use_dividers)
    app.mainloop()


if __name__ == "__main__":
    main()
