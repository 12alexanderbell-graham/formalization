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
        # claim_baseline.txt (run 2026-11-05T1428Z): CLAIMs with inline formulas and no second reading;
        # shrink-only like the formula baseline (the commit that introduces the file may fill it)
        ocb = old(b, "scripts/trust/claim_baseline.txt")
        if ocb is not None:
            cgrown = sorted(set(entries((ROOT / "scripts/trust/claim_baseline.txt").read_text())) - set(entries(ocb)))
            if cgrown:
                print(f"scripts/trust/claim_baseline.txt grew against {b}: {cgrown} (the baseline may only shrink; "
                      f"get a blind second reading of the source instead)")
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
        # Disclosure of independent evidence (run 2026-11-05T0828Z; widened run 2026-11-05T1428Z after
        # blind red team K: d01 declared its self-written "second formulation" as `noncomputable abbrev`,
        # which the old `def`-only pattern did not see; d03 wrote its own "second reading", and second
        # readings had no disclosure rule at all). Every declaration of ANY keyword added to a
        # `Checked/Trust/SecondFormulation*.lean` or `Checked/Trust/SecondReading*.lean` module, and
        # every such module that changed at all, must be named in a LEDGER.md addition together with
        # the word "brief" (who wrote the independent version, and from what, is not machine-checkable).
        DECL = re.compile(r"^[ \t]*(?:@\[[^\]]*\][ \t]*)*(?:(?:private|protected|noncomputable|partial|unsafe|"
                          r"nonrec|scoped|local)[ \t]+)*(?:def|abbrev|theorem|lemma|instance|opaque|structure|class|"
                          r"inductive|irreducible_def|notation|macro|syntax|axiom|example|elab|macro_rules)\b[ \t]*"
                          r"(?:\([^)]*\)[ \t]*)?([^\s({:\[]*)", re.M)
        new_defs = set()
        changed_files = set()
        # every module whose path under Checked/Trust starts with SecondFormulation, SecondReading,
        # Formulations or Transcriptions (at any depth: StatementDeps recognises second formulations and
        # readings by module-name prefix, so `Checked/Trust/SecondReading/X.lean` counts too — adversary
        # of run 1428Z), including modules deleted against the base; the agreements (Formulations*,
        # Transcriptions*) decide which definitions get the mark, so their changes are disclosed too
        PREF = ("SecondFormulation", "SecondReading", "Formulations", "Transcriptions")
        def watched(rel):
            parts = rel.split("/")
            return rel.endswith(".lean") and len(parts) > 2 and parts[0] == "Checked" and parts[1] == "Trust" \
                and parts[2].startswith(PREF)
        r = subprocess.run(["git", "ls-tree", "-r", "--name-only", b, "Checked/Trust"], cwd=ROOT, capture_output=True, text=True)
        rels = {x for x in r.stdout.split() if watched(x)}
        rels |= {str(f.relative_to(ROOT)) for f in (ROOT / "Checked/Trust").rglob("*.lean") if watched(str(f.relative_to(ROOT)))}
        for rel in sorted(rels):
            f = ROOT / rel
            cur = f.read_text() if f.exists() else None
            was = old(b, rel)
            if was != cur:
                changed_files.add(f.name)
            if cur is not None and f.name.startswith(("SecondFormulation", "SecondReading")) or "/Second" in rel:
                now = {d.split(".")[-1] for d in DECL.findall(cur or "") if d}
                prev = {d.split(".")[-1] for d in DECL.findall(was)} if was is not None else set()
                new_defs |= now - prev
        if new_defs or changed_files:
            lo = old(b, "LEDGER.md") or ""
            added = set((ROOT / "LEDGER.md").read_text().splitlines()) - set(lo.splitlines())
            text = "\n".join(added)
            missing = sorted(d for d in new_defs if not re.search(r"(?<![\w.])" + re.escape(d) + r"(?![\w'])", text))
            missing += sorted(f for f in changed_files if f not in text and f[:-5] not in text)
            if missing or not re.search(r"\bbrief\b", text):
                print(f"second formulations/readings added or changed against {b} not disclosed in a LEDGER.md addition "
                      f"naming them (declarations and changed modules) and their blind brief: {missing or sorted(new_defs | changed_files)}")
                fail = True
    print(f"check_formulas: {len(base_now)} baselined FORMULA definitions; {'FAIL' if fail else 'ok'}")
    return 1 if fail else 0


if __name__ == "__main__":
    sys.exit(main())
