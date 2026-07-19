#!/usr/bin/env python3
"""
Vokabel-Quiz — Goethe A1 / Start Deutsch 1 vocabulary trainer
=============================================================

Shows an ENGLISH word and you type the GERMAN translation.
Each word comes with a short example sentence: the English version is
shown as a hint, together with the German sentence with the target word
blanked out (_____). The full German sentence appears once you answer.

Buttons:  Check | Show Answer | Prev | Next, plus Mark/Unmark, a
"Practice: marked only" mode, an Example on/off toggle, skip +/-10, and
Delete word.  Marks and deletions are written back to the .txt file.

This version reads the four-column A1 word-list file
    German  <tab>  English meaning  <tab>  German example  <tab>  English example
(the file "A1_Wortliste_4Spalten.txt" / "A1_Wortliste_Quiz.txt"), with
"--- A ---" letter dividers.  A fifth "Markiert" (1/0) column is added
automatically the first time you mark a word, so your marks are saved.

It also still reads the older "frequency, German, English, ..." files.

Run it with:
    python vokabel_quiz_A1.py

Requirements: just Python 3 with Tkinter (bundled with the standard
python.org installers on Windows/macOS). On Debian/Ubuntu Linux you may
need:  sudo apt install python3-tk

The app looks for the vocabulary file next to this script (or in the
current folder). If it can't find one, a file-open dialog appears so you
can point to any tab-separated word file.
"""

import os
import re
import csv
import tkinter as tk
from tkinter import ttk, filedialog, messagebox

# Files searched for automatically, in order of preference.
DEFAULT_FILENAMES = (
    "A1_Wortliste_Quiz.txt",       # this app's own saved format (with marks)
    "A1_Wortliste_4Spalten.txt",   # the plain 4-column study file
    "Vokabelliste_LiD_Seiten1-12.txt",  # older "Leben in Deutschland" file
)

TRUE_TOKENS = {"1", "*", "x", "true", "yes", "ja", "y"}

# The A1 file's own header/divider text, reused when saving.
A1_HEADER = ["Deutsches Wort (German)", "Bedeutung (English)",
             "Beispielsatz (German)", "Übersetzung (English)",
             "Markiert (1/0)"]
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
            h = list(header or [])[:6]
            h += LID_HEADER[len(h):]
            with open(path, "w", encoding="utf-8", newline="") as f:
                w = csv.writer(f, delimiter="\t", lineterminator="\n")
                w.writerow(h)
                for e in entries:
                    w.writerow([e.get("freq", ""), e["de"], e["en"],
                                "1" if e["marked"] else "0",
                                e.get("ex_de", ""), e.get("ex_en", "")])
            return True

        # a1 format
        h = list(header or [])[:5]
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
                            e.get("ex_en", ""), "1" if e["marked"] else "0"])
        return True
    except OSError:
        return False


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
        self.marked_only = False   # practice mode: all words vs. marked only
        self.show_examples = True  # show the example sentence as a hint
        self.pos = 0
        self.answered = False   # True once Check or Show Answer has been used
        self.correct = 0
        self.attempted = 0

        self._build_ui()
        self.rebuild_order()
        self._show_current()

    def rebuild_order(self):
        """Rebuild the practice sequence for the current mode and reset to start."""
        if self.marked_only:
            self.order = [i for i, e in enumerate(self.entries) if e["marked"]]
        else:
            self.order = list(range(len(self.entries)))
        self.pos = 0

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

        # Study controls: mark toggle + practice-mode toggle
        study = tk.Frame(self, bg="#f4f6f8")
        study.pack(pady=(2, 2))
        self.mark_btn = tk.Button(study, text="☆  Mark", width=14,
                                  command=self.toggle_mark,
                                  bg="#fff4d6", fg="#8a6d00", relief="flat",
                                  font=("Segoe UI", 11, "bold"),
                                  activebackground="#ffe9a8", cursor="hand2")
        self.mark_btn.grid(row=0, column=0, padx=6, ipady=3)
        self.mode_btn = tk.Button(study, text="Practice: All words", width=20,
                                  command=self.toggle_mode,
                                  bg="#e5e9ee", fg="#1f2d3d", relief="flat",
                                  font=("Segoe UI", 11), cursor="hand2")
        self.mode_btn.grid(row=0, column=1, padx=6, ipady=3)
        self.ex_btn = tk.Button(study, text="💡  Example: on", width=16,
                                command=self.toggle_examples,
                                bg="#e5e9ee", fg="#1f2d3d", relief="flat",
                                font=("Segoe UI", 11), cursor="hand2")
        self.ex_btn.grid(row=0, column=2, padx=6, ipady=3)

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
        self.bind("<Control-e>", lambda e: self.toggle_examples())

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
        self._update_mark_ui()
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

    # ---- Mark / practice-mode --------------------------------------------
    def toggle_mark(self):
        """Mark or unmark the current word and persist it to the file."""
        if not self.order:
            return
        item = self._current()
        item["marked"] = not item["marked"]
        if self.path and not self.save_file():
            item["marked"] = not item["marked"]   # revert on write failure
            messagebox.showwarning(
                "Not saved", "Couldn't write the file — the mark was not saved."
            )
            return
        self._update_mark_ui()

    def _update_mark_ui(self):
        """Sync the star indicator and the Mark button label to the word."""
        marked = bool(self.order) and self._current()["marked"]
        self.mark_lbl.config(text="★  marked" if marked else "")
        self.mark_btn.config(text="★  Unmark" if marked else "☆  Mark")

    def toggle_mode(self):
        """Switch between practising all words and only the marked ones."""
        if not self.marked_only:
            if not any(e["marked"] for e in self.entries):
                messagebox.showinfo(
                    "No marked words",
                    "You haven't marked any words yet.\n"
                    "Use “Mark” (or Ctrl+M) on words first."
                )
                return
            self.marked_only = True
        else:
            self.marked_only = False
        self.rebuild_order()
        self.correct = self.attempted = 0
        self._update_mode_ui()
        self._show_current()

    def _update_mode_ui(self):
        self.mode_btn.config(
            text="Practice: Marked only" if self.marked_only
            else "Practice: All words"
        )

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
            if self.entries and self.marked_only:
                messagebox.showinfo(
                    "No marked words left",
                    "That was the last marked word. Switching to all words."
                )
                self.marked_only = False
                self.rebuild_order()
                self._update_mode_ui()
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
