#!/usr/bin/env python3
"""Existing reader modules and their runs/ copies are frozen: a new reading needs a new reader file (run
2026-11-06T1028Z, part 3; check-writer blind to red team N's files, brief written after its report). Blocking in CI (needs --base).

Why: check_blind_route.py runs B1-B4 only on second-version modules whose runs/ copy is NEW since the base.
A `def` appended to an existing `Checked/Trust/SecondReading*.lean` and, in the same commit, to its existing
runs/ copy keeps the two code-identical (check_provenance rule 4 passes) and the copy existed at the base
(check_blind_route returns early): the new "reading" gets no brief, no ordered commits, no answer test. It can
then be registered in literal_readings.txt / literal_slots.txt as if read blind.

  python3 scripts/trust/check_reader_frozen.py --base SHA

F1 (Checked side): every non-generated second-version module (`Checked/Trust/SecondReading*.lean`,
   `SecondFormulation*.lean`, except the generated ones of check_provenance.GENERATED) that exists at SHA is
   unchanged against SHA apart from its module doc (`/-! … -/`, rewritten by authors without numbers, check_prose
   rule 7): no declaration added, removed, renamed or edited, docstrings included. Deleting the module is allowed
   (it removes evidence, which the coverage checks then miss).
F2 (runs/ side): every `.lean` file under `runs/` that exists at SHA and is a reader file at SHA — code-identical
   (check_provenance.code) to a second-version module of SHA, or in a directory that holds a `*brief*.md` at
   SHA — is byte-identical now, or deleted only together with every Checked module that copies it.
F3 (new module from an old reader file): a second-version module added since SHA whose runs/ copy existed at
   SHA must be a copy of that file AS IT WAS AT SHA (F2 then holds it unchanged), so check_blind_route's early
   exit for old reader files only admits readings that were already on record before the push.

A new reading of the same source therefore needs a new reader file in a new folder with its own brief, so
check_blind_route.py B1-B4 apply to it.

Limits: SHA is the push base; within one push an author can still create a reader file, brief and copy in
three commits (check_blind_route.py's business). Module docs stay editable (they carry no code; rule 7 reads
their numbers).
"""
import os
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import check_provenance as P  # noqa: E402

ROOT = Path(__file__).resolve().parents[2]


def without_moddoc(text):
    return re.sub(r"/-!.*?-/", "", text, flags=re.S)


def ls_base(base, prefix):
    out = P.git("ls-tree", "-r", "--name-only", base, "--", prefix) or ""
    return [l for l in out.splitlines() if l.strip()]


def main():
    if "--base" not in sys.argv:
        print("check_reader_frozen: needs --base SHA (existing reader modules and runs/ reader files are frozen against SHA)")
        return 0
    base = sys.argv[sys.argv.index("--base") + 1]
    if P.git("cat-file", "-e", f"{base}^{{commit}}") is None:
        print(f"check_reader_frozen: base {base} not available; skipped")
        return 0
    errors = []
    base_mods = [r for r in ls_base(base, "Checked/Trust") if P.second_module(r) and Path(r).name not in P.GENERATED]
    base_codes = {}
    n1 = 0
    for rel in base_mods:
        old = P.git("show", f"{base}:{rel}") or ""
        base_codes[rel] = P.code(old)
        p = ROOT / rel
        if not p.exists():
            continue
        n1 += 1
        if without_moddoc(p.read_text()) != without_moddoc(old):
            od = {d[0] for d in P.declarations(old)[0]}
            nd = {d[0] for d in P.declarations(p.read_text())[0]}
            what = (f"added {sorted(nd - od)}" if nd - od else "") + (f" removed {sorted(od - nd)}" if od - nd else "")
            errors.append(f"F1: {rel} existed at {base[:12]} and changed outside its module doc"
                          f"{' (' + what.strip() + ')' if what.strip() else ' (a declaration or docstring edited)'}: "
                          f"existing reader modules are frozen — put a new reading in a new reader file with its own "
                          f"brief (check_blind_route.py)")
    # F2: reader files under runs/ at the base
    base_runs = [r for r in ls_base(base, "runs") if r.endswith(".lean")]
    brief_dirs = {str(Path(r).parent) for r in ls_base(base, "runs")
                  if r.endswith(".md") and re.search(r"brief", Path(r).name, re.I)}
    copy_codes = set(base_codes.values())
    n2 = 0
    for r in base_runs:
        old = P.git("show", f"{base}:{r}")
        if old is None:
            continue
        if not (P.code(old) in copy_codes or str(Path(r).parent) in brief_dirs):
            continue
        n2 += 1
        p = ROOT / r
        if not p.exists():
            users = [m for m, c in base_codes.items() if c == P.code(old) and (ROOT / m).exists()]
            if users:
                errors.append(f"F2: reader file {r} deleted while {users} still copy it")
            continue
        if p.read_text() != old:
            errors.append(f"F2: reader file {r} existed at {base[:12]} and was modified: a reader's file is a record of "
                          f"what the blind reader wrote — write a new reading in a new folder with its own brief")
    # F3: new second modules copying an old reader file must copy it as it was at the base
    for rel in P.all_lean():
        if not P.second_module(rel) or Path(rel).name in P.GENERATED or rel in base_codes:
            continue
        code = P.code((ROOT / rel).read_text())
        for c in P.runs_copies(code):
            old = P.git("show", f"{base}:{c}")
            if old is not None and P.code(old) != code:
                errors.append(f"F3: new module {rel} copies {c}, which existed at {base[:12]} with different code")
    for e in errors:
        print(e)
    print(f"check_reader_frozen: {n1} reader modules and {n2} runs/ reader files at {base[:12]} checked; "
          f"{'FAIL' if errors else 'ok'}")
    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main())
