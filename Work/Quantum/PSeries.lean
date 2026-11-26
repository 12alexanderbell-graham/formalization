import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecificLimits.Normed
/-!
# Power series with a geometric coefficient bound (run 2026-11-26T1628Z)

Tools for the H₂⁺ route (`runs/2026-11-26T1628Z/README.md`, section Route): the solutions regular at the singular
points ξ = 1 and η = ±1, and the Taylor steps at regular points, are power series whose coefficients satisfy a
three-term recurrence; a certificate gives |c n| ≤ C qⁿ for every n (finitely many coefficients checked over ℚ,
the rest by induction from the recurrence). Here, generically:

* `summable_of_bound`: ∑ c n xⁿ converges for |x| q < 1;
* `hasDerivAt_of_bound`: on (−r, r) with r q < 1 the sum is differentiable with the termwise derivative;
* `deriv_shift`: the termwise derivative is the power series with coefficients (n + 1) c (n + 1);
* `hasDerivAt_series`: the two combined, so the derivative is again a power series with a geometric bound
  (`bound_deriv`), and the step can be repeated.
-/

namespace Work.Quantum.PSeries
open Set Filter Topology

variable {c : ℕ → ℝ} {C q : ℝ}

theorem summable_of_bound (hc : ∀ n, |c n| ≤ C * q ^ n) (hq : 0 ≤ q) {x : ℝ} (hx : |x| * q < 1) :
    Summable (fun n => c n * x ^ n) := by
  have hg : Summable (fun n : ℕ => C * (|x| * q) ^ n) :=
    (summable_geometric_of_lt_one (by positivity) hx).mul_left C
  refine Summable.of_norm_bounded hg (fun n => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_pow, mul_pow]
  calc |c n| * |x| ^ n ≤ C * q ^ n * |x| ^ n := by gcongr; exact hc n
    _ = C * (|x| ^ n * q ^ n) := by ring

theorem summable_deriv_bound (hq : 0 ≤ q) {r : ℝ} (hr : 0 < r) (hrq : r * q < 1) :
    Summable (fun n : ℕ => C * ((n : ℝ) * q ^ n * r ^ (n - 1))) := by
  have h1 : Summable (fun n : ℕ => (n : ℝ) ^ 1 * (r * q) ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one 1 (by rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]; exact hrq)
  have h2 := (h1.mul_left (C / r))
  refine h2.congr (fun n => ?_)
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    simp only [Nat.add_sub_cancel, mul_pow, pow_succ]
    field_simp

theorem hasDerivAt_of_bound (hc : ∀ n, |c n| ≤ C * q ^ n) (hq : 0 ≤ q) {r : ℝ} (hr : 0 < r)
    (hrq : r * q < 1) {x : ℝ} (hx : x ∈ Ioo (-r) r) :
    HasDerivAt (fun y => ∑' n, c n * y ^ n) (∑' n, c n * ((n : ℝ) * x ^ (n - 1))) x := by
  refine hasDerivAt_tsum_of_isPreconnected (summable_deriv_bound (C := C) hq hr hrq) isOpen_Ioo
    isPreconnected_Ioo (fun n y _ => (hasDerivAt_pow n y).const_mul (c n)) (fun n y hy => ?_)
    (show (0 : ℝ) ∈ Ioo (-r) r from ⟨by linarith, hr⟩)
    (summable_of_bound hc hq (by simp)) hx
  have hy' : |y| ≤ r := abs_le.mpr ⟨hy.1.le, hy.2.le⟩
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, Nat.abs_cast]
  calc |c n| * ((n : ℝ) * |y| ^ (n - 1)) ≤ C * q ^ n * ((n : ℝ) * r ^ (n - 1)) := by
        refine mul_le_mul (hc n) ?_ (by positivity) (le_trans (abs_nonneg _) (hc n))
        gcongr
    _ = C * ((n : ℝ) * q ^ n * r ^ (n - 1)) := by ring

theorem bound_deriv (hc : ∀ n, |c n| ≤ C * q ^ n) (hq : 0 ≤ q) {r : ℝ} (hr : 0 < r) (hrq : r * q < 1) :
    ∃ C' q' : ℝ, 0 ≤ q' ∧ r * q' < 1 ∧
      ∀ n : ℕ, |((n : ℝ) + 1) * c (n + 1)| ≤ C' * q' ^ n := by
  -- (n + 1) qⁿ⁺¹ ≤ K q'ⁿ with q' the midpoint between q and 1 / r
  set q' := (q + 1 / r) / 2 with hq'
  have hqq' : q ≤ q' := by
    have : q * r < 1 := by linarith [mul_comm r q]
    have : q < 1 / r := by rw [lt_div_iff₀ hr]; linarith
    rw [hq']; linarith
  have hq'r : r * q' < 1 := by
    rw [hq']
    have : r * q < 1 := hrq
    field_simp
    nlinarith
  have hq'pos : 0 < q' := by rw [hq']; positivity
  have hratio : q / q' < 1 := by
    rw [div_lt_one hq'pos]
    have : q < 1 / r := by rw [lt_div_iff₀ hr]; linarith [mul_comm r q]
    rw [hq']; linarith
  -- n (q/q')ⁿ is bounded
  have hsum : Summable (fun n : ℕ => (n : ℝ) ^ 1 * (q / q') ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one 1 (by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]; exact hratio)
  obtain ⟨B, hB⟩ : ∃ B, ∀ n : ℕ, (n : ℝ) ^ 1 * (q / q') ^ n ≤ B := by
    obtain ⟨B, hB⟩ := hsum.tendsto_cofinite_zero.bddAbove_range_of_cofinite
    exact ⟨B, fun n => hB ⟨n, rfl⟩⟩
  refine ⟨|C| * q' * (B + 1), q', hq'pos.le, hq'r, fun n => ?_⟩
  have h1 := hc (n + 1)
  have hBn := hB (n + 1)
  rw [pow_one] at hBn
  have hdiv : (q / q') ^ (n + 1) * q' ^ (n + 1) = q ^ (n + 1) := by
    rw [← mul_pow, div_mul_cancel₀ _ hq'pos.ne']
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1)]
  have hCq : |c (n + 1)| ≤ |C| * q ^ (n + 1) :=
    h1.trans (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))
  push_cast at hBn
  calc ((n : ℝ) + 1) * |c (n + 1)| ≤ ((n : ℝ) + 1) * (|C| * q ^ (n + 1)) := by gcongr
    _ = |C| * q' * (((n : ℝ) + 1) * (q / q') ^ (n + 1) * q' ^ n) := by
        rw [← hdiv, pow_succ q']
        field_simp
    _ ≤ |C| * q' * ((B + 1) * q' ^ n) := by
        gcongr
        nlinarith [pow_nonneg (show 0 ≤ q / q' by positivity) (n + 1), pow_nonneg hq'pos.le n]
    _ = |C| * q' * (B + 1) * q' ^ n := by ring

theorem deriv_shift (hc : ∀ n, |c n| ≤ C * q ^ n) (hq : 0 ≤ q) {r : ℝ} (hr : 0 < r) (hrq : r * q < 1)
    {x : ℝ} (hx : |x| ≤ r) :
    ∑' n, c n * ((n : ℝ) * x ^ (n - 1)) = ∑' n : ℕ, ((n : ℝ) + 1) * c (n + 1) * x ^ n := by
  have hs : Summable (fun n => c n * ((n : ℝ) * x ^ (n - 1))) := by
    refine Summable.of_norm_bounded (summable_deriv_bound (C := C) hq hr hrq) (fun n => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, Nat.abs_cast]
    calc |c n| * ((n : ℝ) * |x| ^ (n - 1)) ≤ C * q ^ n * ((n : ℝ) * r ^ (n - 1)) := by
          refine mul_le_mul (hc n) ?_ (by positivity) (le_trans (abs_nonneg _) (hc n))
          gcongr
      _ = C * ((n : ℝ) * q ^ n * r ^ (n - 1)) := by ring
  rw [hs.tsum_eq_zero_add]
  simp only [CharP.cast_eq_zero, zero_mul, mul_zero, zero_add, Nat.cast_add, Nat.cast_one,
    Nat.add_sub_cancel]
  congr 1
  funext n
  ring

/-- The derivative of a power series with a geometric coefficient bound, as a power series. -/
theorem hasDerivAt_series (hc : ∀ n, |c n| ≤ C * q ^ n) (hq : 0 ≤ q) {r : ℝ} (hr : 0 < r)
    (hrq : r * q < 1) {x : ℝ} (hx : x ∈ Ioo (-r) r) :
    HasDerivAt (fun y => ∑' n, c n * y ^ n) (∑' n : ℕ, ((n : ℝ) + 1) * c (n + 1) * x ^ n) x := by
  rw [← deriv_shift hc hq hr hrq (abs_le.mpr ⟨hx.1.le, hx.2.le⟩)]
  exact hasDerivAt_of_bound hc hq hr hrq hx

end Work.Quantum.PSeries
