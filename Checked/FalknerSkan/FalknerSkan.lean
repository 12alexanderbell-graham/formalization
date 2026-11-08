import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Checked.Homann.Homann
import Checked.Blasius.Blasius
import Checked.FalknerSkan.FSScale
/-! Falkner–Skan rows, `FalknerSkan`: two rows of the Falkner–Skan wall-shear table, obtained from the certified Homann and Blasius theorems by the similarity scaling with c the square root of two: existence of a solution of the half-β problem with wall shear in the window printed in the statement of `fs_half_exists`, and the window printed in the statement of `fs_zero_wall_shear` for the wall shear of every solution of the β-zero problem; uniqueness of the half-β solution is not formalised. Promoted from `Work/FalknerSkan/FalknerSkan.lean`. -/

namespace Checked.FalknerSkan
open Set Filter Topology
open Checked.FalknerSkan.FSScale

/-- Falkner–Skan β = 1/2, existence: there is a solution f of f''' + f f'' + (1 − f'²)/2 = 0 on
[0, ∞) (f has derivative p, p has derivative q, q has derivative −f q − (1 − p²)/2, one-sided
at 0) with f(0) = 0, p(0) = 0 and p(η) → 1 as η → ∞ whose wall value q(0) = f''(0) lies
strictly between 0.927680039 and 0.927680040. -/
theorem fs_half_exists : ∃ f p q : ℝ → ℝ,
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η) ∧
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η) ∧
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - 1 / 2 * (1 - p η ^ 2)) (Ici 0) η) ∧
    f 0 = 0 ∧ p 0 = 0 ∧ Tendsto p atTop (𝓝 1) ∧
    0.927680039 < q 0 ∧ q 0 < 0.927680040 := by
  obtain ⟨f, p, q, hf, hp, hq, f0, p0, lim, lo, hi⟩ := Checked.Homann.homann_exists
  have hq' : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(2 * f η * q η) - 1 * (1 - p η ^ 2)) (Ici 0) η :=
    fun η hη => (hq η hη).congr_deriv (by ring)
  have hc : (0 : ℝ) < Real.sqrt 2 := by positivity
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  obtain ⟨A, B, C⟩ := scale hc hf hp hq'
  refine ⟨_, _, _, A, B, fun s hs => (C s hs).congr_deriv (by rw [h2]; ring), ?_, ?_,
    scale_lim hc lim, ?_, ?_⟩
  · simp [f0]
  · simp [p0]
  · show 0.927680039 < q (0 / Real.sqrt 2) / Real.sqrt 2
    rw [zero_div, lt_div_iff₀ hc]
    nlinarith [sqrt2_lt]
  · show q (0 / Real.sqrt 2) / Real.sqrt 2 < 0.927680040
    rw [zero_div, div_lt_iff₀ hc]
    nlinarith [lt_sqrt2]

/-- Falkner–Skan β = 0, wall shear: for every solution f of f''' + f f'' = 0 on [0, ∞) (f has
derivative p, p has derivative q, q has derivative −f q, one-sided at 0) with f(0) = 0,
p(0) = 0 and p(η) → 1 as η → ∞, the wall value q(0) = f''(0) lies between 0.4695999883610
and 0.4695999883611. -/
theorem fs_zero_wall_shear (f p q : ℝ → ℝ)
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η)) (Ici 0) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = 0) (hlim : Tendsto p atTop (𝓝 1)) :
    0.4695999883610 ≤ q 0 ∧ q 0 ≤ 0.4695999883611 := by
  have hq' : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(1 * f η * q η) - 0 * (1 - p η ^ 2)) (Ici 0) η :=
    fun η hη => (hq η hη).congr_deriv (by ring)
  have hc : (0 : ℝ) < Real.sqrt 2 := by positivity
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  obtain ⟨A, B, C⟩ := scale hc hf hp hq'
  have key := Checked.Blasius.blasius_wall_shear _ _ _ A B
    (fun s hs => (C s hs).congr_deriv (by rw [h2]; ring)) (by simp [hf0]) (by simp [hp0])
    (scale_lim hc hlim)
  simp only [zero_div] at key
  obtain ⟨k1, k2⟩ := key
  have e : q 0 = Real.sqrt 2 * (q 0 / Real.sqrt 2) := by field_simp
  have hq0 : 0 ≤ q 0 / Real.sqrt 2 := le_trans (by norm_num) k1
  rw [e]
  constructor <;> nlinarith [sqrt2_le', le_sqrt2']

end Checked.FalknerSkan
