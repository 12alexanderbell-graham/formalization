#!/usr/bin/env python3
"""Run 2026-11-07T1628Z: promote the weighted one-sided Blasius chain to Checked.
Work/Sim/OneSided3.lean -> Checked/Sim/OneSided3.lean; Work/Blasius/{BCellW,BWData}.lean -> Checked/Blasius/;
Checked/Blasius/Blasius.lean imports BWData instead of BQData (statements untouched; the script asserts
the two headline statements and all theorem headers of Blasius.lean are unchanged);
Checked/Blasius/BQData.lean is moved to _archive/ (not deleted). Module docs: number-free (check_prose rule 7)."""
import re, os, subprocess
R = '/home/claude/formalization/'
def rd(p): return open(R + p, encoding='utf-8').read()
def wr(p, t): open(R + p, 'w', encoding='utf-8').write(t)

def moddoc(t, new):
    return re.sub(r"/-!.*?-/", lambda m: new, t, count=1, flags=re.S)

# OneSided3
t = rd('Work/Sim/OneSided3.lean').replace('Work.Sim.OneSided3', 'Checked.Sim.OneSided3')
t = moddoc(t, "/-! Validated simulation, `OneSided3`: the logarithmic-norm (one-sided Lipschitz) cell step for "
  "systems of three components, in a weighted norm with two positive weights; a Sylvester (LDL) criterion "
  "for a symmetric quadratic form in three variables; the triangle inequality for the weighted norm. "
  "Promoted from `Work/Sim/OneSided3.lean`. -/")
assert 'import Mathlib\n' not in t
wr('Checked/Sim/OneSided3.lean', t)

# BCellW
t = rd('Work/Blasius/BCellW.lean')
imports = ["Mathlib.Algebra.Order.Star.Real", "Mathlib.Analysis.InnerProductSpace.Basic",
           "Mathlib.Analysis.LocallyConvex.AbsConvexOpen", "Mathlib.Topology.Algebra.Module.ModuleTopology",
           "Mathlib.Analysis.SpecialFunctions.ExpDeriv",
           "Mathlib.Tactic.NormNum", "Mathlib.Tactic.Linarith", "Mathlib.Tactic.Ring", "Mathlib.Tactic.FieldSimp",
           "Mathlib.Tactic.Positivity", "Checked.Sim.QPoly", "Checked.Sim.OneSided3"]
t = re.sub(r"\A(import [^\n]*\n)+", "".join(f"import {i}\n" for i in imports), t)
t = t.replace('Work.Sim.OneSided3', 'Checked.Sim.OneSided3').replace('Work.Blasius.BCellW', 'Checked.Blasius.BCellW')
t = moddoc(t, "/-! Blasius boundary layer, `BCellW`: validated cells of the Blasius system in a weighted norm, whose "
  "error grows only with a one-sided bound of the field certified per cell by Sylvester's criterion at the two "
  "ends of the range of the approximation's third component, so that the damping term contracts instead of "
  "counting as growth; every numeric condition of a cell is one proposition over the rationals decided by kernel "
  "evaluation, and a chain of cells is one Boolean. Promoted from `Work/Blasius/BCellW.lean`. -/")
t = t.replace("/-- The determinant of the symmetric 3×3 matrix with entries m11 … m33. -/",
              "/-- The determinant of the symmetric matrix of order three with entries m11 … m33. -/")
wr('Checked/Blasius/BCellW.lean', t)

# BWData
t = rd('Work/Blasius/BWData.lean').replace('Work.Blasius.BCellW', 'Checked.Blasius.BCellW').replace(
    'namespace Work.Blasius.BWData', 'namespace Checked.Blasius.BWData').replace(
    'end Work.Blasius.BWData', 'end Checked.Blasius.BWData')
t = moddoc(t, "/-! Blasius boundary layer, `BWData`: the weighted cells of the Blasius initial-value problem with unit "
  "wall value of q, checked by kernel evaluation, and the resulting enclosure of the state at the end of the chain "
  "(the same end values as the earlier sup-norm chain). Promoted from `Work/Blasius/BWData.lean`. -/")
assert 'Work.' not in t
wr('Checked/Blasius/BWData.lean', t)

# Blasius.lean
old = rd('Checked/Blasius/Blasius.lean')
new = old.replace('import Checked.Blasius.BQData\n', 'import Checked.Blasius.BWData\n').replace('BQData.', 'BWData.')
hdr = lambda s: re.findall(r"^theorem[^\n]*(?:\n    [^\n]*)*?:= by", s, re.M)
assert hdr(old) == hdr(new) and old != new
wr('Checked/Blasius/Blasius.lean', new)

# Checked.lean
c = rd('Checked.lean')
c = c.replace('import Checked.Blasius.BQData\n', 'import Checked.Sim.OneSided3\nimport Checked.Blasius.BCellW\nimport Checked.Blasius.BWData\n')
wr('Checked.lean', c)
os.makedirs(R + '_archive/Checked/Blasius', exist_ok=True)
subprocess.run(['git', 'mv', 'Checked/Blasius/BQData.lean', '_archive/Checked/Blasius/BQData.lean'], cwd=R, check=True)
print('promoted')
