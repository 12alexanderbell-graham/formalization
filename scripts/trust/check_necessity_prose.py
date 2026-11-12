#!/usr/bin/env python3
"""Prose claims about hypothesis necessity cite the machine-checked classification (run 2026-11-12T1228Z).

Why: the module doc of `Checked.Chemistry.RKAcentric` recorded a referee's sentence "`b < v_c` and `b < v_l` are
essential". No script read it (module docs are frozen by hash, which keeps a sentence from changing but not from
being wrong). Run 2026-11-12T1228Z proved `b < v_l` REDUNDANT (`Checked.Trust.MaxwellRight.rk_coexistence_unique_r7`).
Since run 2026-11-09T0628Z the necessity of every hypothesis is classified by machine-checked witnesses in
`TRUST_MAP.md`; a hand-written sentence saying a hypothesis is essential, needed, necessary, redundant, harmless or
implied by the others competes with that generated layer.

Rule N-P1: in `Checked/**/*.lean` outside `Checked/Trust/` (where witness modules live), a comment paragraph (lines
between blank lines) containing such a word must also contain `TRUST_MAP` or a backticked `Checked.Trust.` name,
so the reader is sent to the checked classification. Paragraphs written before this rule are listed in
`scripts/trust/necessity_prose_baseline.txt` (file and first matching line, whitespace-normalised; shrink-only).

Limits: a word list (a paraphrase such as "cannot be dropped" passes); the cited classification is not compared with
the sentence (a reader still has to read TRUST_MAP.md); docstrings of spec fields count as comment text.
Usage: python3 scripts/trust/check_necessity_prose.py   (exit 1 on a new uncited paragraph or a stale baseline line)
"""
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
BASELINE = ROOT / "scripts/trust/necessity_prose_baseline.txt"
WORDS = re.compile(
    r"\b(essential|redundant|harmless|implied by the others|necessary|"
    r"(?:is|are|is not|are not) needed)\b", re.IGNORECASE)
CITE = re.compile(r"TRUST_MAP|`Checked\.Trust\.")


def comment_paragraphs(text):
    """Yield (first line number, paragraph text) of comment blocks (/-! … -/, /-- … -/, -- lines)."""
    lines = text.splitlines()
    in_block = False
    para, start = [], None
    for i, line in enumerate(lines, 1):
        s = line.strip()
        is_comment = in_block or s.startswith("/-") or s.startswith("--")
        if s.startswith("/-") and "-/" not in s[2:]:
            in_block = True
        elif in_block and "-/" in s:
            in_block = False
            is_comment = True
        if is_comment and s and s not in ("/-!", "/--", "-/"):
            if start is None:
                start = i
            para.append(line)
        else:
            if para:
                yield start, para
            para, start = [], None
    if para:
        yield start, para


def norm(s):
    return " ".join(s.split())


def main():
    base = set()
    if BASELINE.exists():
        for l in BASELINE.read_text().splitlines():
            if l.strip() and not l.startswith("#"):
                base.add(norm(l))
    found, problems = set(), []
    for p in sorted((ROOT / "Checked").rglob("*.lean")):
        rel = p.relative_to(ROOT).as_posix()
        if rel.startswith("Checked/Trust/"):
            continue
        for start, para in comment_paragraphs(p.read_text()):
            text = "\n".join(para)
            if not WORDS.search(text) or CITE.search(text):
                continue
            first = next(l for l in para if WORDS.search(l))
            key = norm(f"{rel} | {first}")
            found.add(key)
            if key not in base:
                problems.append(f"{rel}:{start}: a necessity claim in prose without a citation of TRUST_MAP.md or a "
                                f"`Checked.Trust.` witness: {norm(first)}")
    stale = sorted(base - found)
    for s in stale:
        problems.append(f"stale baseline line (remove it: the baseline only shrinks): {s}")
    print(f"check_necessity_prose: {len(found)} uncited necessity paragraphs ({len(found & base)} baselined); "
          f"{len(problems)} problems")
    for pr in problems:
        print("  " + pr)
    return 1 if problems else 0


if __name__ == "__main__":
    sys.exit(main())
