#!/usr/bin/env python3
"""d02: the exclusion baseline (P9/P12) is keyed by the EXACT reader line.  A second, differently worded blind reading of
the same definitions (new folder, own BRIEF.md) restates three excluded overclaims in other words; P9 forces every line
of a cited reader file into the registry (and the baseline cannot grow), so the template prints them."""
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
d = root/"runs/2026-11-09T1628Z/clauses2"
d.mkdir(parents=True)
(d/"BRIEF.md").write_text("""# Brief: second blind clause reader for three pinned definitions (run 2026-11-09T1628Z)

The program shows, in the plain-words phrase of a pinned definition, short clauses written by blind readers
(`runs/2026-11-09T0228Z/clauses/BRIEF.md` describes the task). A second, independent reading of three definitions
is wanted: `Checked.Chemistry.CubicEOS.IsCriticalIsotherm` (p v, `criticalSpec_pins`),
`Checked.Chemistry.Coexistence.IsMaxwellCoexistence` (p vl vg ps, `maxwellSpec_pins`) and
`Checked.Cosmography.BambaK.omega0` (K a t₀, `omega0Spec_pins`).

## What you may read
`Checked/Fidelity/*.lean` (the specifications and pinning theorems) and the Lean source of the three definitions.

## What you must NOT read
`scripts/`, every `*.md` file other than this brief, `validation/`, `runs/` (except this folder), `Work/`, `_archive/`,
the git history, the web.

## Output (write exactly one file: `runs/2026-11-09T1628Z/clauses2/CLAUSES2.txt`)
For each definition 0 to 3 lines `CLAUSE | <full Lean name> | <clause>`: plain English, no formula characters, one
fact each that the specification or pinning theorem fixes. Then `END` and a short note.
""", encoding="utf-8")
(d/"CLAUSES2.txt").write_text("""CLAUSE | Checked.Chemistry.CubicEOS.IsCriticalIsotherm | an inflection point of the isotherm with horizontal tangent
CLAUSE | Checked.Chemistry.Coexistence.IsMaxwellCoexistence | the same as the two phases having equal chemical potential
CLAUSE | Checked.Cosmography.BambaK.omega0 | above one exactly when the curvature constant is positive
END
Each clause is the content of the pinning theorem in other words.
""", encoding="utf-8")
reg = root/"scripts/trust/phrase_roles.txt"
o5 = "CLAUSE | Checked.Cosmography.Aviles.cosmoCoeff | The order 5 coefficient is the lerk parameter usually written l\n"
sub1(reg, o5, o5 + "# source: runs/2026-11-09T1628Z/clauses2/CLAUSES2.txt\n"
     "CLAUSE | Checked.Chemistry.CubicEOS.IsCriticalIsotherm | an inflection point of the isotherm with horizontal tangent\n"
     "CLAUSE | Checked.Chemistry.Coexistence.IsMaxwellCoexistence | the same as the two phases having equal chemical potential\n"
     "CLAUSE | Checked.Cosmography.BambaK.omega0 | above one exactly when the curvature constant is positive\n")
regen(root)
ledger(root, "- 2026-11-09, run 2026-11-09T1628Z — **IsCriticalIsotherm, IsMaxwellCoexistence, omega0 phrases regenerated** after a second blind clause reading (`runs/2026-11-09T1628Z/clauses2/`) was added to the registry; phrases rewritten by `check_claims.py --generate`.")
