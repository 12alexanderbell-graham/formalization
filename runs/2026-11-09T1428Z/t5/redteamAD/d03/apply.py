#!/usr/bin/env python3
"""d03: a second, honest reader of the cosmoCoeff formula (same kind of narrow reader as the SYMBOLS reader).  Both its
lines are true.  The generator drops line 1 (contained in a text already shown) and glues line 2 ("divided by ...") to
the last text shown, which is the SYMBOLS clause for order 5.  Follows the registry's route: new folder with its own
BRIEF.md, reading, then the registry block (route commits are the author's business and not reproduced here)."""
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
d = root/"runs/2026-11-09T1628Z/formula"
d.mkdir(parents=True)
(d/"BRIEF.md").write_text("""# Brief: blind reader of the cosmographic coefficient formula (run 2026-11-09T1628Z)

**Purpose.** The plain-words phrase of the pinned definition `Checked.Cosmography.Aviles.cosmoCoeff n a t`
(binders: `n` the derivative order of the coefficient, `a` the scale factor, `t` the time of evaluation) is built only
from texts written by blind readers (rules P3 to P11 of `scripts/trust/check_claims.py`). A second blind reading of the
formula of this one definition is wanted. Your answer is compared mechanically with other readers' texts.

## What you may read
- The Lean source of `cosmoCoeff` (find it with grep under `Checked/`; its signature and body only, not its docstring)
  and the specification `Checked/Fidelity/RedshiftCoeffSpecs.lean` (structure `CosmoCoeffSpecCore`, theorem
  `cosmoCoeffCore_pins`).

## What you must NOT read
`scripts/`, every `*.md` file other than this brief, `validation/`, `runs/` (except this folder), `Work/`, `_archive/`,
the git history, the web.

## Output (write exactly one file: `runs/2026-11-09T1628Z/formula/FORMULA.txt`)
Two lines, in plain English (no formula characters, no comma or semicolon, the binder `n` may be named):

    CLAUSE | Checked.Cosmography.Aviles.cosmoCoeff | <the numerator of the defining quotient>
    CLAUSE | Checked.Cosmography.Aviles.cosmoCoeff | <the denominator, starting with the words divided by>

Then `END` and a short note on anything uncertain.
""", encoding="utf-8")
(d/"FORMULA.txt").write_text("""CLAUSE | Checked.Cosmography.Aviles.cosmoCoeff | n-th time derivative of the scale factor over the scale factor
CLAUSE | Checked.Cosmography.Aviles.cosmoCoeff | divided by the Hubble rate to the power n
END
Both lines read from the Lean body: iteratedDeriv n a t divided by a t times hubble a t to the power n.
""", encoding="utf-8")
reg = root/"scripts/trust/phrase_roles.txt"
o5 = "CLAUSE | Checked.Cosmography.Aviles.cosmoCoeff | The order 5 coefficient is the lerk parameter usually written l\n"
sub1(reg, o5, o5 + "# source: runs/2026-11-09T1628Z/formula/FORMULA.txt\n"
     "CLAUSE | Checked.Cosmography.Aviles.cosmoCoeff | n-th time derivative of the scale factor over the scale factor\n"
     "CLAUSE | Checked.Cosmography.Aviles.cosmoCoeff | divided by the Hubble rate to the power n\n")
regen(root)
ledger(root, "- 2026-11-09, run 2026-11-09T1628Z — **Aviles.cosmoCoeff phrase regenerated** after a second blind reading of its formula (`runs/2026-11-09T1628Z/formula/`) was added to the registry; phrase rewritten by `check_claims.py --generate`.")
