import Checked.Trust.NonVacuity
import Checked.FalknerSkan.NegReversedWallShear
import Checked.FalknerSkan.NegWallShear

/-!
# Hypothesis necessity witnesses, the printed reverse-flow wall value (trust track T2b, run 2026-11-11T1828Z)

For the overshoot statement of the printed reverse-flow Falkner–Skan wall value: the wall value itself is
needed (the attached fast-approach solution has every other property and its velocity never exceeds the edge
value), and so are the two derivative links `p' = q` (a constant velocity profile with a linear shear) and the
equation for `q` (a quadratic stream function with constant shear). In each witness the velocity stays at or
below the edge value, so the conclusion is false.
-/

open Set Filter Topology

namespace Checked.Trust.NCR

/-- The wall-value hypothesis is needed: the attached solution of `fs_neg_wall_shear_exists_decay` has
increasing velocity tending to the edge value, so it never overshoots. -/
theorem fs_neg_reversed_printed_overshoots_h6 :
    necessity% Checked.FalknerSkan.NegReversedWallShear.fs_neg_reversed_printed_overshoots 6 := by
  obtain ⟨f, p, q, hf, hp, hq, hf0, hp0, hlim, hpos, -⟩ :=
    Checked.FalknerSkan.NegWallShear.fs_neg_wall_shear_exists_decay
  have hmono : MonotoneOn p (Ici 0) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := q) (convex_Ici 0)
      (HasDerivWithinAt.continuousOn (fun x hx => hp x hx)) (fun x hx => ?_) (fun x hx => ?_)
    · exact (hp x (interior_subset hx)).mono interior_subset
    · exact (hpos x (interior_subset hx)).le
  refine ⟨f, p, q, hf, hp, hq, hf0, hp0, ?_⟩
  rintro ⟨η, hη, h1⟩
  have hη' : η ∈ Ici (0 : ℝ) := mem_Ici.2 hη.le
  have : p η ≤ 1 := ge_of_tendsto hlim
    (eventually_atTop.2 ⟨η, fun t ht => hmono hη' (mem_Ici.2 (hη.le.trans ht)) ht⟩)
  linarith

/-- The link `p' = q` is needed: `f = 0`, `p = 0` and the linear shear `q = −0.005158 + 0.1988 η` meet every
other hypothesis, and the velocity never exceeds the edge value. -/
theorem fs_neg_reversed_printed_overshoots_h2 :
    necessity% Checked.FalknerSkan.NegReversedWallShear.fs_neg_reversed_printed_overshoots 2 := by
  refine ⟨fun _ => 0, fun _ => 0, fun η => -0.005158 + 1988 / 10000 * η, fun η _ => ?_, fun η _ => ?_,
    by norm_num, rfl, by norm_num, ?_⟩
  · exact hasDerivWithinAt_const _ _ _
  · have h := ((hasDerivAt_id η).const_mul (1988 / 10000 : ℝ)).const_add (-0.005158 : ℝ)
    exact h.hasDerivWithinAt.congr_deriv (by ring)
  · rintro ⟨η, -, h⟩; norm_num at h

/-- The equation for `q` is needed: `f = −0.005158 η² / 2`, `p = −0.005158 η`, `q = −0.005158` meet every
other hypothesis, and the velocity is never positive. -/
theorem fs_neg_reversed_printed_overshoots_h3 :
    necessity% Checked.FalknerSkan.NegReversedWallShear.fs_neg_reversed_printed_overshoots 3 := by
  refine ⟨fun η => -0.005158 * η ^ 2 / 2, fun η => -0.005158 * η, fun _ => -0.005158, fun η _ => ?_,
    fun η _ => ?_, by norm_num, by norm_num, rfl, ?_⟩
  · have h := ((hasDerivAt_pow 2 η).const_mul (-0.005158 : ℝ)).div_const 2
    exact h.hasDerivWithinAt.congr_deriv (by ring)
  · have h := (hasDerivAt_id η).const_mul (-0.005158 : ℝ)
    exact h.hasDerivWithinAt.congr_deriv (by ring)
  · rintro ⟨η, hη, h⟩
    have : (0 : ℝ) < η := hη
    nlinarith

end Checked.Trust.NCR
