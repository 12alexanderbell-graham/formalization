#!/usr/bin/env python3
"""FORMULA second-formulation baseline guard (run 2026-11-05T0828Z; red team J, defects d03, d06).

A headline may rest on a FORMULA definition (def_kinds.txt) only if the definition has a
machine-checked agreement with a blind second formulation (`Checked/Trust/Formulations*.lean`,
checked by scripts/trust/StatementDeps.lean) or is listed in scripts/trust/formula_baseline.txt.
The baseline holds the FORMULA definitions that existed before the rule and have no second
formulation yet. It may only shrink:

  python3 scripts/trust/check_formulas.py              format check
  python3 scripts/trust/check_formulas.py --base SHA   also: no line added to the baseline against
                                                       SHA, and no FORMULA definition added to
                                                       def_kinds.txt against SHA is baselined

(A new FORMULA definition therefore needs its second formulation in the same push.)

With --base, every definition ADDED to a `Checked/Trust/SecondFormulation*.lean` module against SHA
must be named (last name component) in a line added to LEDGER.md, with the path of the blind brief
it was written from: who wrote a second formulation, and from what, is not machine-checkable, so it
is disclosed (a second formulation written by the author of the definition checks nothing).
"""
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
BASELINE = "scripts/trust/formula_baseline.txt"
KINDS = "scripts/trust/def_kinds.txt"
NAME = re.compile(r"^[A-Za-z_][\w.'₀-₉]*$")


def entries(text):
    return [l.strip() for l in text.splitlines() if l.strip() and not l.strip().startswith("#")]


def kinds_of(text):
    out = {}
    for l in entries(text):
        parts = l.split()
        if len(parts) == 2:
            out[parts[0]] = parts[1]
    return out


def old(base, rel):
    r = subprocess.run(["git", "show", f"{base}:{rel}"], cwd=ROOT, capture_output=True, text=True)
    return None if r.returncode else r.stdout


def main():
    fail = False
    p = ROOT / BASELINE
    if not p.exists():
        print(f"{BASELINE} is missing (it may be empty, but it must exist)")
        return 1
    base_now = entries(p.read_text())
    kinds_now = kinds_of((ROOT / KINDS).read_text())
    seen = set()
    for l in base_now:
        if not NAME.match(l):
            print(f"{BASELINE}: bad line `{l}` (one full constant name per line)")
            fail = True
        if l in seen:
            print(f"{BASELINE}: duplicate line `{l}`")
            fail = True
        seen.add(l)
        if kinds_now.get(l) not in ("FORMULA", "MATH", "WITNESS", "PRINTED"):
            print(f"{BASELINE}: `{l}` is not classified FORMULA, MATH, WITNESS or PRINTED in {KINDS}")
            fail = True
    if "--base" in sys.argv:
        b = sys.argv[sys.argv.index("--base") + 1]
        ob = old(b, BASELINE)
        if ob is not None:
            grown = sorted(set(base_now) - set(entries(ob)))
            if grown:
                print(f"{BASELINE} grew against {b}: {grown} (the baseline may only shrink; "
                      f"write a blind second formulation instead)")
                fail = True
        # (the commit that introduces the baseline may list relabelled grandfathered definitions)
        ok = old(b, KINDS) if ob is not None else None
        kinds_old = kinds_of(ok) if ok is not None else None
        added_formulas = set() if kinds_old is None else {n for n, k in kinds_now.items() if k in ("FORMULA", "MATH", "WITNESS", "PRINTED") and kinds_old.get(n) != k}
        bad = sorted(added_formulas & set(base_now))
        if bad:
            print(f"FORMULA definitions added to {KINDS} against {b} are baselined: {bad} "
                  f"(a new FORMULA needs its blind second formulation in the same push)")
            fail = True
    if "--base" in sys.argv:
        b = sys.argv[sys.argv.index("--base") + 1]
        DEF = re.compile(r"^(?:noncomputable\s+)?def\s+([^\s({:]+)", re.M)
        new_defs = set()
        for f in sorted((ROOT / "Checked/Trust").glob("SecondFormulation*.lean")):
            rel = str(f.relative_to(ROOT))
            now = set(DEF.findall(f.read_text()))
            was = old(b, rel)
            new_defs |= now - (set(DEF.findall(was)) if was is not None else set())
        if new_defs:
            lo = old(b, "LEDGER.md") or ""
            added = set((ROOT / "LEDGER.md").read_text().splitlines()) - set(lo.splitlines())
            text = "\n".join(added)
            missing = sorted(d for d in new_defs if not re.search(r"(?<![\w.])" + re.escape(d) + r"(?![\w'])", text))
            if missing or "brief" not in text:
                print(f"second formulations added against {b} not disclosed in a LEDGER.md addition naming them "
                      f"and their blind brief: {missing or sorted(new_defs)}")
                fail = True
    print(f"check_formulas: {len(base_now)} baselined FORMULA definitions; {'FAIL' if fail else 'ok'}")
    return 1 if fail else 0


if __name__ == "__main__":
    sys.exit(main())
