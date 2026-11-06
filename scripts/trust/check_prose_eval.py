#!/usr/bin/env python3
"""Headline docstrings may not grade a model, a correlation or a source (run 2026-11-06T1028Z, part 3;
written AFTER reading red team N, not blind). Blocking in CI; reads .lake/meaning.jsonl.

Why: red team N d05 wrapped a true bound on Soave's κ(ω) polynomial (κ < 2 on [0, 1]) in the docstring
"… so the correlation is reliable over the whole range". Every number and name in it was backed, so no
check read the one word that carried the false claim: no Lean statement certifies that a model or a
correlation is reliable, accurate, realistic or in agreement with experiment (annex XLI: "follows from
the model", never "nature does"). Such grades are judgments a scientist must make, not certified output.

Rule E1: the docstring of a registered headline (meaning.jsonl rows with a `doc`) contains none of the
grading words below (case-insensitive, whole words): reliable/reliability/unreliable, trustworthy,
robust(ly/ness), realistic(ally), faithful(ly), accurate(ly)/inaccurate, adequate(ly)/adequacy,
physically sound/meaningful/correct/reasonable, agree(s) with experiment(s)/data/observation(s)/measurement(s),
consistent with experiment(s)/data/observation(s)/measurement(s), validated against, confirmed by experiment(s)/data/
observation(s). Exact quantitative words ("accuracy" of a stated number of decimals) are not in the list.
Grandfathered findings: `scripts/trust/prose_eval_baseline.txt` (`<headline> | <word>`), shrink-only with
--base (empty when the rule was written: no headline used such a word).

Limits: a grade written without a listed word ("can be used safely", "works well") passes; the list
only grows.
"""
import json
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
BASE = ROOT / "scripts/trust/prose_eval_baseline.txt"
W = re.compile(r"\b(?:un)?reliab(?:le|ly|ility)\b|\btrustworth\w*|\brobust(?:ly|ness)?\b|\brealistic(?:ally)?\b"
               r"|\bfaithful(?:ly)?\b|\b(?:in)?accurate(?:ly)?\b|\badequa(?:te|tely|cy)\b"
               r"|\bphysically\s+(?:sound|meaningful|correct|reasonable)\b"
               r"|\b(?:agrees?|consistent)\s+with\s+(?:the\s+)?(?:experiments?|data|observations?|measurements?)\b"
               r"|\bvalidated\s+against\b|\bconfirmed\s+by\s+(?:the\s+)?(?:experiments?|data|observations?)\b", re.I)


def entries(text):
    return [l.strip() for l in text.splitlines() if l.strip() and not l.startswith("#")]


def main():
    rows = [json.loads(l) for l in (ROOT / ".lake/meaning.jsonl").read_text().splitlines() if l.strip()]
    found = []
    for r in rows:
        for m in W.finditer(r.get("doc") or ""):
            found.append(f"{r['name']} | {m.group(0).lower()}")
    base = entries(BASE.read_text()) if BASE.exists() else []
    errs = [f"E1: {f.split(' | ')[0]}: its docstring grades a model, correlation or source ('{f.split(' | ')[1]}'); "
            f"no statement certifies that: say what the statement proves" for f in found if f not in base]
    if "--base" in sys.argv:
        b = sys.argv[sys.argv.index("--base") + 1]
        old = subprocess.run(["git", "show", f"{b}:scripts/trust/prose_eval_baseline.txt"], cwd=ROOT,
                             capture_output=True, text=True)
        if old.returncode == 0:
            added = set(base) - set(entries(old.stdout))
            errs += [f"E2: {BASE.name}: line added against {b[:12]} (shrink-only): {a}" for a in sorted(added)]
        elif base:
            errs.append(f"E2: {BASE.name} did not exist at {b[:12]}: it must start empty")
    for e in errs:
        print(e)
    print(f"check_prose_eval: {len(rows)} meaning rows, {len(found)} grading words ({len(found) - len([e for e in errs if e.startswith('E1')])} baselined); "
          + ("FAIL" if errs else "ok"))
    sys.exit(1 if errs else 0)


if __name__ == "__main__":
    main()
