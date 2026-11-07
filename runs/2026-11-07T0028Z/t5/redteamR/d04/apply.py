#!/usr/bin/env python3
"""d04: new headline Checked.Math.GelfandPDERange.gelfand_pde_radial_range_exists: statement of
gelfand_pde_radial_exists (dimension 3); paraphrase starts "In dimension 2," -- the numeral 2 is a numeral of the
generated claim (the order of differentiability), so V6 accepts it. usage: apply.py <repo_root>"""
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

/-! Gelfand problem in the unit ball as a PDE: the range of the parameter for which a radial classical
solution exists, restated in a module of its own. -/

namespace Checked.Math.GelfandPDERange
open Set Filter Topology InnerProductSpace Laplacian Metric

/-- In dimension 2, for every `lam` with 0 < `lam` ≤ 3.321992118 there is a function `u`, twice
continuously differentiable on the open unit ball, continuous on the closed unit ball, zero on the
unit sphere and a function of `‖x‖` alone on the closed ball, with `Δ u x + lam * Real.exp (u x) = 0`
at each `x` in the open ball. -/
theorem gelfand_pde_radial_range_exists (lam : ℝ) (hpos : 0 < lam) (hle : lam ≤ 3.321992118) :
    ∃ u : EuclideanSpace ℝ (Fin 3) → ℝ,
      ContDiffOn ℝ 2 u (ball 0 1) ∧
      ContinuousOn u (closedBall 0 1) ∧
      (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → u x = 0) ∧
      (∃ g : ℝ → ℝ, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, u x = g ‖x‖) ∧
      (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ u x + lam * Real.exp (u x) = 0) :=
  Checked.Math.GelfandPDEExists.gelfand_pde_radial_exists lam hpos hle

theorem nv_gelfand_pde_radial_range_exists :
    nonvacuity% Checked.Math.GelfandPDERange.gelfand_pde_radial_range_exists :=
  ⟨1, by norm_num, by norm_num, trivial⟩

end Checked.Math.GelfandPDERange
'''

new = root / "Checked/Math/GelfandPDERange.lean"
assert not new.exists()
new.write_text(LEAN, encoding="utf-8")
append("Checked.lean", "import Checked.Math.GelfandPDERange\n")
append("scripts/trust/headlines.txt",
       "# Gelfand PDE, parameter range (run 2026-11-07T0228Z)\nChecked.Math.GelfandPDERange.gelfand_pde_radial_range_exists\n")
R = "Checked.Trust.SecondReading."
append("scripts/trust/literal_readings.txt",
       "Checked.Math.GelfandPDERange.gelfand_pde_radial_range_exists " +
       " ".join(R + c for c in ["gelfandPdeSpace", "gelfandPdeBall", "gelfandPdeClosedBall", "gelfandPdeRegular",
                               "gelfandPdeContinuous", "gelfandPdeLamRange"]) + "\n")
append("scripts/trust/prose_vocab.txt", "twice\ncontinuously\nopen\nunit\nsphere\nalone\ndimension\n")
append("LEDGER.md",
       "\n## Run 2026-11-07T0228Z (author, part 5)\n"
       "- New headline `gelfand_pde_radial_range_exists` (module `Checked.Math.GelfandPDERange`, headlines.txt): the statement of `gelfand_pde_radial_exists` "
       "restated in a module of its own (proof: that theorem); NV witness `nv_gelfand_pde_radial_range_exists` in the same module.\n"
       "- Literal readings (literal_readings.txt) for `gelfand_pde_radial_range_exists`: gelfandPdeSpace, gelfandPdeBall, gelfandPdeClosedBall, "
       "gelfandPdeRegular, gelfandPdeContinuous, gelfandPdeLamRange, the constants of `Checked/Trust/SecondReadingGelfandPDE.lean` "
       "(reading f9bd980, unchanged), as registered for the existence headline.\n"
       "- prose_vocab.txt: added the words `twice`, `continuously`, `open`, `unit`, `sphere`, `alone`, `dimension` for the paraphrase of the Gelfand PDE headlines "
       "(they describe the ball, its boundary, the dimension of the space and the regularity of u; none is an inference, generality, persistence or strength word, V2).\n")
print("d04 applied")
