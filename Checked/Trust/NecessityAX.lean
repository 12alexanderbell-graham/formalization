import Checked.Cosmography.FREta
import Checked.Trust.NecessityAW

/-! Hypothesis necessity for `Checked.Cosmography.FREta.eta_ratios` (run 2026-11-19T0628Z).
The model hypothesis (the metric F(R) setting) is NEEDED: take the flat model with matter and a
cosmological constant at matter density minus one (the hyperbolic cosine to the power two thirds of
`Checked.Trust.NecessityAW`), keep its scale factor, and replace F by the constant function one. The other
three hypotheses then hold at density parameter zero (F is never zero, the corrected quantity and the
jerk combination are nonzero at that model's deceleration, jerk, snap and lerk), the second derivative
of F is zero, and the first ratio of the review is not zero. Open: hypotheses three and four. In the flat
matter-plus-constant family with F equal to R plus a constant (every model of `Checked.Trust.NecessityAW`)
the corrected quantity is a negative multiple of the squared density times a quadratic with no real root,
and the jerk combination is a negative multiple of the density, so each vanishes only at density zero (de
Sitter space), where both vanish together: neither hypothesis can be dropped alone inside that family, and
a witness needs a scale factor or an F outside it. -/

namespace Checked.Trust.NecessityAX
open Checked.Cosmography Checked.Cosmography.Aviles Checked.Cosmography.FRCosmo Checked.Cosmography.FREta

/-- The metric F(R) setting is needed in `eta_ratios`: the scale factor of the matter-plus-constant model
at matter density minus one with F the constant one. -/
theorem eta_ratios_h1 : necessity% Checked.Cosmography.FREta.eta_ratios 1 := by
  obtain ⟨a, t₀, -, hq, hj, hs, hl, -⟩ := Checked.Trust.NecessityAW.facts_nonpos (Ω := -1) (by norm_num)
  refine ⟨0, a, fun _ => 1, t₀, ?_⟩
  simp only [hq, hj, hs, hl]
  have d2 : deriv^[2] (fun _ : ℝ => (1 : ℝ)) (curv a t₀) = 0 := by
    simp [Function.iterate_succ, deriv_const']
  refine ⟨one_ne_zero, by unfold correctR; norm_num, by norm_num, fun h => ?_⟩
  have h1 := h.1
  rw [d2] at h1
  unfold eta20Of P2 Q2 P0 Q0 at h1
  norm_num at h1

end Checked.Trust.NecessityAX
