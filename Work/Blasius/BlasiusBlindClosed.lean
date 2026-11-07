import Mathlib
import Work.Blasius.BlasiusBlind
import Work.Blasius.Blasius

/-!
# Blasius wall shear: the blind restatement, closed

The blind restater's `Blind.Blasius.wall_shear_bounds` (run 2026-11-07T1228Z: f is C³ on
[0, ∞), the equation f''' + (1/2) f f'' = 0 with one-sided `derivWithin` on [0, ∞), f(0) = 0,
f'(0) = 0, f' → 1) follows from the program's frozen `Work.Blasius.blasius_wall_shear`
(f, p, q with derivatives within [0, ∞), no regularity beyond that) with p, q the first and
second `derivWithin` of f.
-/

namespace Work.Blasius.BlindClosed
open Set Filter Topology

theorem wall_shear_bounds (f : ℝ → ℝ) (hf : Blind.Blasius.IsBlasiusSolution f) :
    (0.33205733621519 : ℝ) ≤ derivWithin (derivWithin f (Ici 0)) (Ici 0) 0 ∧
    derivWithin (derivWithin f (Ici 0)) (Ici 0) 0 ≤ (0.33205733621520 : ℝ) := by
  obtain ⟨hC, hode, hf0, hp0, hlim⟩ := hf
  have hU : UniqueDiffOn ℝ (Ici (0 : ℝ)) := uniqueDiffOn_Ici 0
  set p := derivWithin f (Ici 0) with hpdef
  set q := derivWithin p (Ici 0) with hqdef
  have hC1 : ContDiffOn ℝ 2 p (Ici 0) := hC.derivWithin hU (by norm_num)
  have hC2 : ContDiffOn ℝ 1 q (Ici 0) := hC1.derivWithin hU (by norm_num)
  refine Work.Blasius.blasius_wall_shear f p q (fun η hη => ?_) (fun η hη => ?_)
    (fun η hη => ?_) hf0 hp0 hlim
  · exact ((hC.differentiableOn (by norm_num)) η hη).hasDerivWithinAt
  · exact ((hC1.differentiableOn (by norm_num)) η hη).hasDerivWithinAt
  · have h := ((hC2.differentiableOn (by norm_num)) η hη).hasDerivWithinAt
    have e := hode η hη
    refine h.congr_deriv ?_
    linear_combination e

end Work.Blasius.BlindClosed
