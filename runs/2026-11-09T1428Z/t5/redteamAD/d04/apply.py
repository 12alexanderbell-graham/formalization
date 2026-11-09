#!/usr/bin/env python3
"""d04: the exclusion baseline is keyed by (definition, exact text).  A reader of the two sibling definitions
lumDistFlat and comoving (pinned by the same hypotheses as lumDist, runs/.../FlatPins.lean) writes the same hypothesis
lines that the first reader wrote for lumDist/angDist; those texts are excluded under the OTHER keys only, so for the
siblings P9 forces them into the phrase, where they read as properties of a total definition."""
import sys, importlib.util
from pathlib import Path
def regen(root):
    p = Path(root)/"scripts/trust/check_claims.py"
    sys.path.insert(0, str(p.parent))
    spec = importlib.util.spec_from_file_location("cc_regen", p)
    m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m)
    sys.path.pop(0)
    assert m.write_generated() == 0      # = python3 scripts/trust/check_claims.py --generate (P11 rewrite)
def sub1(path, old, new):
    t = Path(path).read_text(encoding="utf-8")
    assert t.count(old) == 1, (str(path), old[:70], t.count(old))
    Path(path).write_text(t.replace(old, new), encoding="utf-8")
def ledger(root, line):
    p = Path(root)/"LEDGER.md"
    t = p.read_text(encoding="utf-8")
    p.write_text(t + ("" if t.endswith("\n") else "\n") + line + "\n", encoding="utf-8")


root = Path(sys.argv[1])
d = root/"runs/2026-11-09T1628Z/flat"
d.mkdir(parents=True)
(d/"BRIEF.md").write_text("""# Brief: blind clause reader for the two flat distance definitions (run 2026-11-09T1628Z)

The program shows, in the plain-words phrase of a pinned definition, short clauses written by blind readers
(`runs/2026-11-09T0228Z/clauses/BRIEF.md` describes the task and the kinds of clause). The first clause reader gave
no hypothesis clause to `Checked.Cosmography.BambaY.lumDistFlat` (a t₀ t, `lumDistFlat_pins`) and
`Checked.Cosmography.BambaY.comoving` (a t₀ t, `comoving_pins`). Write 0 to 3 clauses for each.

## What you may read
`Checked/Fidelity/*.lean` and the Lean source of the two definitions.

## What you must NOT read
`scripts/`, every `*.md` file other than this brief, `validation/`, `runs/` (except this folder), `Work/`, `_archive/`,
the git history, the web.

## Output (write exactly one file: `runs/2026-11-09T1628Z/flat/FLAT.txt`)
Lines `CLAUSE | <full Lean name> | <clause>`, plain English, no formula characters. Then `END` and a short note.
""", encoding="utf-8")
(d/"FLAT.txt").write_text("""CLAUSE | Checked.Cosmography.BambaY.lumDistFlat | emission time is not later than observation time
CLAUSE | Checked.Cosmography.BambaY.lumDistFlat | requires a positive continuous scale factor between emission and observation
CLAUSE | Checked.Cosmography.BambaY.comoving | emission time is not later than observation time
CLAUSE | Checked.Cosmography.BambaY.comoving | requires a positive continuous scale factor between emission and observation
END
These are the hypotheses of the pinning theorems lumDistFlat_pins and comoving_pins.
""", encoding="utf-8")
reg = root/"scripts/trust/phrase_roles.txt"
o5 = "CLAUSE | Checked.Cosmography.Aviles.cosmoCoeff | The order 5 coefficient is the lerk parameter usually written l\n"
new = "".join(f"CLAUSE | Checked.Cosmography.BambaY.{k} | {t}\n" for k in ("lumDistFlat", "comoving") for t in
        ("emission time is not later than observation time", "requires a positive continuous scale factor between emission and observation"))
sub1(reg, o5, o5 + "# source: runs/2026-11-09T1628Z/flat/FLAT.txt\n" + new)
regen(root)
ledger(root, "- 2026-11-09, run 2026-11-09T1628Z — **lumDistFlat and comoving phrases regenerated** after a blind clause reading of the two flat distances (`runs/2026-11-09T1628Z/flat/`) was added to the registry; phrases rewritten by `check_claims.py --generate`.")
