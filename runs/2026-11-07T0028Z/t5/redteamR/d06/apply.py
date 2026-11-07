#!/usr/bin/env python3
"""d06: new headline Checked.Math.GelfandPDEBound.gelfand_pde_radial_parameter_bound: the nonexistence statement with
the weak bound lam <= 4 (a one-number certified target), paraphrase "... and this bound is sharp", the word 'sharp'
added to prose_vocab.txt with its LEDGER line. usage: apply.py <repo_root>"""
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
import Checked.Math.GelfandPDE
import Checked.Math.GelfandPDEExists
import Checked.Trust.NonVacuity

/-! Gelfand problem in the unit ball as a PDE: a bound on the parameter of a radial classical solution. -/

namespace Checked.Math.GelfandPDEBound
open Set Filter Topology InnerProductSpace Laplacian Metric

/-- If `u` is twice continuously differentiable on the open unit ball, continuous on the closed unit
ball, zero on the unit sphere, a function of `‖x‖` alone on the closed ball and
`Δ u x + lam * Real.exp (u x) = 0` at each `x` in the open ball, then `lam ≤ 4`, and this bound is sharp. -/
theorem gelfand_pde_radial_parameter_bound (lam : ℝ) (u : EuclideanSpace ℝ (Fin 3) → ℝ)
    (hu : ContDiffOn ℝ 2 u (ball 0 1))
    (hc : ContinuousOn u (closedBall 0 1))
    (hb : ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → u x = 0)
    (hrad : ∃ g : ℝ → ℝ, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, u x = g ‖x‖)
    (hpde : ∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ u x + lam * Real.exp (u x) = 0) :
    lam ≤ 4 := by
  have h := Checked.Math.GelfandPDE.gelfand_pde_radial_bound lam u hu hc hb hrad hpde
  exact h.trans (by norm_num)

theorem nv_gelfand_pde_radial_parameter_bound :
    nonvacuity% Checked.Math.GelfandPDEBound.gelfand_pde_radial_parameter_bound := by
  obtain ⟨u, hu, hc, hb, hrad, hpde⟩ :=
    Checked.Math.GelfandPDEExists.gelfand_pde_radial_exists 3.321992118 (by norm_num) le_rfl
  exact ⟨3.321992118, u, hu, hc, hb, hrad, hpde, trivial⟩

end Checked.Math.GelfandPDEBound
'''

new = root / "Checked/Math/GelfandPDEBound.lean"
assert not new.exists()
new.write_text(LEAN, encoding="utf-8")
append("Checked.lean", "import Checked.Math.GelfandPDEBound\n")
append("scripts/trust/headlines.txt",
       "# Gelfand PDE, parameter bound (run 2026-11-07T0228Z)\nChecked.Math.GelfandPDEBound.gelfand_pde_radial_parameter_bound\n")
R = "Checked.Trust.SecondReading."
append("scripts/trust/literal_readings.txt",
       "Checked.Math.GelfandPDEBound.gelfand_pde_radial_parameter_bound " +
       " ".join(R + c for c in ["gelfandPdeSpace", "gelfandPdeBall", "gelfandPdeClosedBall", "gelfandPdeRegular",
                               "gelfandPdeContinuous"]) + "\n")
append("scripts/trust/prose_vocab.txt", "twice\ncontinuously\nopen\nunit\nsphere\nalone\nsharp\n")
append("LEDGER.md",
       "\n## Run 2026-11-07T0228Z (author, part 5)\n"
       "- New headline `gelfand_pde_radial_parameter_bound` (module `Checked.Math.GelfandPDEBound`, headlines.txt): the hypotheses of `gelfand_pde_radial_bound`, "
       "conclusion λ ≤ 4 (proof: that theorem and 3.321992119 ≤ 4); NV witness `nv_gelfand_pde_radial_parameter_bound` in the same module.\n"
       "- Literal readings (literal_readings.txt) for `gelfand_pde_radial_parameter_bound`: gelfandPdeSpace, gelfandPdeBall, gelfandPdeClosedBall, "
       "gelfandPdeRegular, gelfandPdeContinuous, the constants of `Checked/Trust/SecondReadingGelfandPDE.lean` (reading f9bd980, unchanged), as registered for the bound headline.\n"
       "- prose_vocab.txt: added the words `twice`, `continuously`, `open`, `unit`, `sphere`, `alone`, `sharp` for the paraphrase of the Gelfand PDE headlines "
       "(ball, boundary, regularity; `sharp` for the bound of the pair, which the existence headline matches to nine decimals; none is an inference, generality, "
       "persistence or strength word, V2).\n")
print("d06 applied")
