import Mathlib
import Checked.FalknerSkan.SeparationPrinted

/-!
# Blind restatement of the printed-value comparison, closed (run 2026-11-11T0828Z)

The definition and theorem below are the blind restater's text (Sonnet, from the claim in words only,
`runs/2026-11-11T0828Z/blind/`), namespaced; the proof derives it from the headline.
-/

open Filter Set

namespace Blind.SepPrinted

structure IsSepProfile (β : ℝ) (f f1 f2 f3 : ℝ → ℝ) : Prop where
  d1 : ∀ x ∈ Ici (0 : ℝ), HasDerivWithinAt f (f1 x) (Ici 0) x
  d2 : ∀ x ∈ Ici (0 : ℝ), HasDerivWithinAt f1 (f2 x) (Ici 0) x
  d3 : ∀ x ∈ Ici (0 : ℝ), HasDerivWithinAt f2 (f3 x) (Ici 0) x
  ode : ∀ x ∈ Ici (0 : ℝ), f3 x + f x * f2 x + β * (1 - (f1 x) ^ 2) = 0
  f_zero : f 0 = 0
  f1_zero : f1 0 = 0
  outer : Tendsto f1 atTop (nhds 1)
  wall_shear : f2 0 = 0
  f2_pos : ∀ x, 0 < x → 0 < f2 x
  superexp : ∀ M : ℝ, ∀ᶠ x in atTop, M * (1 - f1 x) ≤ f2 x

theorem blind_sep_printed :
    ¬ ∃ f f1 f2 f3 : ℝ → ℝ, IsSepProfile (-0.1988376) f f1 f2 f3 := by
  rintro ⟨f, f1, f2, f3, h⟩
  have hq : ∀ x ∈ Ici (0 : ℝ), HasDerivWithinAt f2
      (-(f x * f2 x) - (-0.1988376 : ℝ) * (1 - f1 x ^ 2)) (Ici 0) x := by
    intro x hx
    refine (h.d3 x hx).congr_deriv ?_
    linarith [h.ode x hx]
  exact Checked.FalknerSkan.SeparationPrinted.fs_separation_not_printed_value h.d1 h.d2 hq h.f_zero h.f1_zero
    h.wall_shear h.outer (fun x hx => h.f2_pos x hx) h.superexp (by norm_num)

end Blind.SepPrinted

#print axioms Blind.SepPrinted.blind_sep_printed
