#!/usr/bin/env python3
"""d01: new headline Checked.Math.GelfandPDERegular.gelfand_pde_radial_regular_exists: byte-identical statement of
gelfand_pde_radial_exists (ContDiffOn ℝ 2 u (ball 0 1)); the paraphrase says "three times continuously
differentiable". V6 accepts the 3 (the claim has Fin 3), V10 binds a numeral only through the word adjacent to it:
"three times" is adjacent to "times", which is not a disclosed-vocabulary word, so the BIND for "continuously"
(ContDiff ℝ n) is never consulted. usage: apply.py <repo_root>"""
import sys
from pathlib import Path

root = Path(sys.argv[1])


def append(rel, text):
    p = root / rel
    old = p.read_text(encoding="utf-8")
    if not old.endswith("\n"):
        old += "\n"
    p.write_text(old + text, encoding="utf-8")


LEAN = '''import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.PiL2
import Checked.Math.GelfandPDEExists
import Checked.Trust.NonVacuity

/-! Gelfand problem in the unit ball of three-dimensional space as a PDE: the regularity of the radial
classical solutions of `Checked.Math.GelfandPDEExists.gelfand_pde_radial_exists`, restated in a module of its
own. -/

namespace Checked.Math.GelfandPDERegular
open Set Filter Topology InnerProductSpace Laplacian Metric

/-- For every `lam` with 0 < `lam` ≤ 3.321992118 there is a function `u`, three times continuously
differentiable on the open unit ball, continuous on the closed unit ball, zero on the unit sphere and a
function of `‖x‖` on the closed ball, with `Δ u x + lam * Real.exp (u x) = 0` at each `x` in the open
ball (`Δ` is Mathlib's Laplacian). -/
theorem gelfand_pde_radial_regular_exists (lam : ℝ) (hpos : 0 < lam) (hle : lam ≤ 3.321992118) :
    ∃ u : EuclideanSpace ℝ (Fin 3) → ℝ,
      ContDiffOn ℝ 2 u (ball 0 1) ∧
      ContinuousOn u (closedBall 0 1) ∧
      (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → u x = 0) ∧
      (∃ g : ℝ → ℝ, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, u x = g ‖x‖) ∧
      (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ u x + lam * Real.exp (u x) = 0) :=
  Checked.Math.GelfandPDEExists.gelfand_pde_radial_exists lam hpos hle

theorem nv_gelfand_pde_radial_regular_exists :
    nonvacuity% Checked.Math.GelfandPDERegular.gelfand_pde_radial_regular_exists :=
  ⟨1, by norm_num, by norm_num, trivial⟩

end Checked.Math.GelfandPDERegular
'''

new = root / "Checked/Math/GelfandPDERegular.lean"
assert not new.exists()
new.write_text(LEAN, encoding="utf-8")
append("Checked.lean", "import Checked.Math.GelfandPDERegular\n")
append("scripts/trust/headlines.txt",
       "# Gelfand PDE, regularity of the radial solutions (run 2026-11-07T1628Z)\n"
       "Checked.Math.GelfandPDERegular.gelfand_pde_radial_regular_exists\n")
R = "Checked.Trust.SecondReading."
append("scripts/trust/literal_readings.txt",
       "Checked.Math.GelfandPDERegular.gelfand_pde_radial_regular_exists " +
       " ".join(R + c for c in ["gelfandPdeSpace", "gelfandPdeBall", "gelfandPdeClosedBall", "gelfandPdeRegular",
                               "gelfandPdeContinuous", "gelfandPdeLamRange"]) + "\n")
append("LEDGER.md",
       "\n## Run 2026-11-07T1628Z (author, part 5)\n"
       "- New headline `gelfand_pde_radial_regular_exists` (module `Checked.Math.GelfandPDERegular`, headlines.txt): the statement of "
       "`gelfand_pde_radial_exists` restated in a module of its own (proof: that theorem); NV witness "
       "`nv_gelfand_pde_radial_regular_exists` in the same module.\n"
       "- Literal readings (literal_readings.txt) for `gelfand_pde_radial_regular_exists`: gelfandPdeSpace, gelfandPdeBall, gelfandPdeClosedBall, "
       "gelfandPdeRegular, gelfandPdeContinuous, gelfandPdeLamRange, the constants of `Checked/Trust/SecondReadingGelfandPDE.lean` "
       "(reading f9bd980, unchanged), as registered for the existence headline.\n")
print("d01 applied")
