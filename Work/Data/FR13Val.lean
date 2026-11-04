import Mathlib
import Work.Data.FR13Certs

/-! Proof tools for `Work.Data.FR13`: continuity, value bounds, logarithm bounds. -/

namespace Work.Data.FR13Val
open Work.Data.FR13Tools Work.Data.FR13Certs

theorem cont_margChi {n : ℕ} (tbl : Fin n → ℝ × ℝ × ℝ) (Hb σ : ℝ) (hσ : 0 < σ) :
    Continuous fun Ω => margChi tbl Hb σ Ω := by
  have he : (fun Ω => margChi tbl Hb σ Ω) = fun Ω => (S0 tbl + Hb ^ 2 / σ ^ 2)
      - (S1 tbl Ω + Hb / σ ^ 2) ^ 2 / (S2 tbl Ω + 1 / σ ^ 2)
      + Real.log (σ ^ 2 * (S2 tbl Ω + 1 / σ ^ 2)) := funext fun Ω => margChi_closed _ _ _ _ hσ
  rw [he]
  have hS1 : Continuous (S1 tbl) := by unfold S1 esq; fun_prop
  have hS2 : Continuous (S2 tbl) := by unfold S2 esq; fun_prop
  have hpos : ∀ Ω, 0 < S2 tbl Ω + 1 / σ ^ 2 := fun Ω => by
    have : 0 ≤ S2 tbl Ω := Finset.sum_nonneg fun i _ => div_nonneg (sq_nonneg _) (sq_nonneg _)
    positivity
  refine (continuous_const.sub (((hS1.add continuous_const).pow 2).div (hS2.add continuous_const)
    fun Ω => (hpos Ω).ne')).add ((continuous_const.mul (hS2.add continuous_const)).log fun Ω => ?_)
  exact mul_ne_zero (by positivity) (hpos Ω).ne'

theorem val_lower {n : ℕ} (tbl : Fin n → ℝ × ℝ × ℝ) (hz : ∀ i, 0 ≤ (tbl i).1)
    (hh : ∀ i, 0 ≤ (tbl i).2.1) (Hb σ p0 p1 β0 β1 a b : ℝ) (s : Fin n → ℝ)
    (hσ : 0 < σ) (hHb : 0 ≤ Hb) (hP0 : P0 tbl = p0) (hP1 : P1 tbl = p1) (hs : ∀ i, 0 < s i)
    (ha0 : 0 ≤ a) (hb1 : b ≤ 1) (hT0 : T0 tbl s ≤ β0) (hT1 : T1 tbl s ≤ β1)
    (Ω : ℝ) (ha : a ≤ Ω) (hb : Ω ≤ b) :
    (S0 tbl + Hb ^ 2 / σ ^ 2) - ((β0 + Hb / σ ^ 2) + β1 * b) ^ 2 / ((p0 + 1 / σ ^ 2) + p1 * a)
      + Real.log (σ ^ 2 * ((p0 + 1 / σ ^ 2) + p1 * a)) ≤ margChi tbl Hb σ Ω := by
  have h0 : 0 ≤ Ω := ha0.trans ha
  have h1 : Ω ≤ 1 := hb.trans hb1
  rw [margChi_closed _ _ _ _ hσ, S2_lin tbl hz h0 h1, hP0, hP1]
  have hσ2 : 0 < σ ^ 2 := by positivity
  have hP0n : 0 ≤ p0 := hP0 ▸ Finset.sum_nonneg fun i _ => div_nonneg zero_le_one (sq_nonneg _)
  have hP1n : 0 ≤ p1 := hP1 ▸ Finset.sum_nonneg fun i _ => div_nonneg (by
    have : 1 ≤ (1 + (tbl i).1) ^ 3 := one_le_pow₀ (by linarith [hz i])
    linarith) (sq_nonneg _)
  have hT1n : 0 ≤ T1 tbl s := Finset.sum_nonneg fun i _ => div_nonneg (mul_nonneg (hh i) (by
    have : 1 ≤ (1 + (tbl i).1) ^ 3 := one_le_pow₀ (by linarith [hz i])
    linarith)) (by have := hs i; positivity)
  have hS1 := S1_le tbl hz hh s hs h0 h1
  have hS1n := S1_nonneg tbl hh Ω
  have hAa : 0 < (p0 + 1 / σ ^ 2) + p1 * a := by positivity
  have hAΩ : (p0 + 1 / σ ^ 2) + p1 * a ≤ p0 + p1 * Ω + 1 / σ ^ 2 := by nlinarith
  have hB : S1 tbl Ω + Hb / σ ^ 2 ≤ (β0 + Hb / σ ^ 2) + β1 * b := by nlinarith
  have hB2 : (S1 tbl Ω + Hb / σ ^ 2) ^ 2 ≤ ((β0 + Hb / σ ^ 2) + β1 * b) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hB 2
  have hd : (S1 tbl Ω + Hb / σ ^ 2) ^ 2 / (p0 + p1 * Ω + 1 / σ ^ 2)
      ≤ ((β0 + Hb / σ ^ 2) + β1 * b) ^ 2 / ((p0 + 1 / σ ^ 2) + p1 * a) :=
    div_le_div₀ (sq_nonneg _) hB2 hAa hAΩ
  have hl : Real.log (σ ^ 2 * ((p0 + 1 / σ ^ 2) + p1 * a)) ≤ Real.log (σ ^ 2 * (p0 + p1 * Ω + 1 / σ ^ 2)) :=
    Real.log_le_log (by positivity) (mul_le_mul_of_nonneg_left hAΩ hσ2.le)
  linarith

theorem val_upper {n : ℕ} (tbl : Fin n → ℝ × ℝ × ℝ) (hz : ∀ i, 0 ≤ (tbl i).1)
    (hh : ∀ i, 0 ≤ (tbl i).2.1) (Hb σ p0 p1 blo Ωr : ℝ) (sR : Fin n → ℝ)
    (hσ : 0 < σ) (hHb : 0 ≤ Hb) (hP0 : P0 tbl = p0) (hP1 : P1 tbl = p1) (hsR : ∀ i, 0 < sR i)
    (hr0 : 0 ≤ Ωr) (hr1 : Ωr ≤ 1) (hlo : blo ≤ Lsum tbl sR Ωr) (hblo : 0 ≤ blo) :
    margChi tbl Hb σ Ωr ≤ (S0 tbl + Hb ^ 2 / σ ^ 2) - (blo + Hb / σ ^ 2) ^ 2 / ((p0 + 1 / σ ^ 2) + p1 * Ωr)
      + Real.log (σ ^ 2 * ((p0 + 1 / σ ^ 2) + p1 * Ωr)) := by
  rw [margChi_closed _ _ _ _ hσ, S2_lin tbl hz hr0 hr1, hP0, hP1]
  have hσ2 : 0 < σ ^ 2 := by positivity
  have hP0n : 0 ≤ p0 := hP0 ▸ Finset.sum_nonneg fun i _ => div_nonneg zero_le_one (sq_nonneg _)
  have hP1n : 0 ≤ p1 := hP1 ▸ Finset.sum_nonneg fun i _ => div_nonneg (by
    have : 1 ≤ (1 + (tbl i).1) ^ 3 := one_le_pow₀ (by linarith [hz i])
    linarith) (sq_nonneg _)
  have hL := S1_ge tbl hz hh sR hsR hr0 hr1
  have hA : 0 < (p0 + 1 / σ ^ 2) + p1 * Ωr := by positivity
  have e : p0 + p1 * Ωr + 1 / σ ^ 2 = (p0 + 1 / σ ^ 2) + p1 * Ωr := by ring
  rw [e]
  have hB2 : (blo + Hb / σ ^ 2) ^ 2 ≤ (S1 tbl Ωr + Hb / σ ^ 2) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 2
  have := div_le_div_of_nonneg_right hB2 hA.le
  linarith

/-- Logarithm to high accuracy from the Mercator series around 8. -/
theorem log_near (y : ℝ) (hy : 0 < y) (h : |1 - y / 8| < 1) (n : ℕ) :
    |Real.log y - (3 * Real.log 2 - ∑ i ∈ Finset.range n, (1 - y / 8) ^ (i + 1) / (i + 1))|
      ≤ |1 - y / 8| ^ (n + 1) / (1 - |1 - y / 8|) := by
  have key := Real.abs_log_sub_add_sum_range_le h n
  have hl : Real.log y = 3 * Real.log 2 + Real.log (1 - (1 - y / 8)) := by
    rw [show 1 - (1 - y / 8) = y / 8 by ring, Real.log_div hy.ne' (by norm_num),
      show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    push_cast; ring
  rw [hl]
  convert key using 2
  ring


theorem log_near' (y x : ℝ) (hy : 0 < y) (hx : x = 1 - y / 8) (h0 : 0 ≤ x) (h1 : x < 1) (n : ℕ) :
    |Real.log y - (3 * Real.log 2 - ∑ i ∈ Finset.range n, x ^ (i + 1) / (i + 1))|
      ≤ x ^ (n + 1) / (1 - x) := by
  have h := log_near y hy (by rw [← hx, abs_of_nonneg h0]; exact h1) n
  rwa [← hx, abs_of_nonneg h0] at h

/-- Lower bound for the value of the marginalised chi-square on [a, b]: a rational check of a
concave quadratic at both ends (`ell` is a lower bound for log(σ²A(a))). -/
theorem val_lower2 {n : ℕ} (tbl : Fin n → ℝ × ℝ × ℝ) (hz : ∀ i, 0 ≤ (tbl i).1)
    (hh : ∀ i, 0 ≤ (tbl i).2.1) (Hb σ p0 p1 β0 β1 a b v ell : ℝ) (s : Fin n → ℝ)
    (hσ : 0 < σ) (hHb : 0 ≤ Hb) (hP0 : P0 tbl = p0) (hP1 : P1 tbl = p1) (hs : ∀ i, 0 < s i)
    (ha0 : 0 ≤ a) (hb1 : b ≤ 1) (hT0 : T0 tbl s ≤ β0) (hT1 : T1 tbl s ≤ β1)
    (hell : ell ≤ Real.log (σ ^ 2 * ((p0 + 1 / σ ^ 2) + p1 * a)))
    (hqa : 0 < ((S0 tbl + Hb ^ 2 / σ ^ 2) - v + ell + 1) * ((p0 + 1 / σ ^ 2) + p1 * a)
      - ((β0 + Hb / σ ^ 2) + β1 * a) ^ 2 - ((p0 + 1 / σ ^ 2) + p1 * a))
    (hqb : 0 < ((S0 tbl + Hb ^ 2 / σ ^ 2) - v + ell + 1) * ((p0 + 1 / σ ^ 2) + p1 * b)
      - ((β0 + Hb / σ ^ 2) + β1 * b) ^ 2 - ((p0 + 1 / σ ^ 2) + p1 * a))
    (Ω : ℝ) (ha : a ≤ Ω) (hb : Ω ≤ b) : v < margChi tbl Hb σ Ω := by
  have h0 : 0 ≤ Ω := ha0.trans ha
  have h1 : Ω ≤ 1 := hb.trans hb1
  have hq := quad_pos ((S0 tbl + Hb ^ 2 / σ ^ 2) - v + ell + 1) (p0 + 1 / σ ^ 2) p1
    (β0 + Hb / σ ^ 2) β1 ((p0 + 1 / σ ^ 2) + p1 * a) a b Ω ha hb hqa hqb
  rw [margChi_closed _ _ _ _ hσ, S2_lin tbl hz h0 h1, hP0, hP1]
  have hσ2 : 0 < σ ^ 2 := by positivity
  have hP0n : 0 ≤ p0 := hP0 ▸ Finset.sum_nonneg fun i _ => div_nonneg zero_le_one (sq_nonneg _)
  have hP1n : 0 ≤ p1 := hP1 ▸ Finset.sum_nonneg fun i _ => div_nonneg (by
    have : 1 ≤ (1 + (tbl i).1) ^ 3 := one_le_pow₀ (by linarith [hz i])
    linarith) (sq_nonneg _)
  have hS1 := S1_le tbl hz hh s hs h0 h1
  have hS1n := S1_nonneg tbl hh Ω
  have hAa : 0 < (p0 + 1 / σ ^ 2) + p1 * a := by positivity
  set A := p0 + p1 * Ω + 1 / σ ^ 2 with hA
  have hAΩ : (p0 + 1 / σ ^ 2) + p1 * a ≤ A := by rw [hA]; nlinarith
  have hApos : 0 < A := lt_of_lt_of_le hAa hAΩ
  have hB : S1 tbl Ω + Hb / σ ^ 2 ≤ (β0 + Hb / σ ^ 2) + β1 * Ω := by nlinarith
  have hB2 : (S1 tbl Ω + Hb / σ ^ 2) ^ 2 ≤ ((β0 + Hb / σ ^ 2) + β1 * Ω) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hB 2
  have hd : (S1 tbl Ω + Hb / σ ^ 2) ^ 2 / A ≤ ((β0 + Hb / σ ^ 2) + β1 * Ω) ^ 2 / A :=
    div_le_div_of_nonneg_right hB2 hApos.le
  have hlog : Real.log (σ ^ 2 * A) - Real.log (σ ^ 2 * ((p0 + 1 / σ ^ 2) + p1 * a))
      ≥ 1 - ((p0 + 1 / σ ^ 2) + p1 * a) / A := by
    rw [← Real.log_div (by positivity) (by positivity)]
    have : σ ^ 2 * A / (σ ^ 2 * ((p0 + 1 / σ ^ 2) + p1 * a)) = A / ((p0 + 1 / σ ^ 2) + p1 * a) := by
      field_simp
    rw [this]
    have h := Real.one_sub_inv_le_log_of_pos (div_pos hApos hAa)
    rw [inv_div] at h; linarith
  have e2 : (p0 + 1 / σ ^ 2) + p1 * Ω = A := by rw [hA]; ring
  rw [e2] at hq
  have h3 : 0 < ((S0 tbl + Hb ^ 2 / σ ^ 2) - v + ell + 1) - ((β0 + Hb / σ ^ 2) + β1 * Ω) ^ 2 / A
      - ((p0 + 1 / σ ^ 2) + p1 * a) / A := by
    have : ((S0 tbl + Hb ^ 2 / σ ^ 2) - v + ell + 1) - ((β0 + Hb / σ ^ 2) + β1 * Ω) ^ 2 / A
        - ((p0 + 1 / σ ^ 2) + p1 * a) / A
        = (((S0 tbl + Hb ^ 2 / σ ^ 2) - v + ell + 1) * A - ((β0 + Hb / σ ^ 2) + β1 * Ω) ^ 2
          - ((p0 + 1 / σ ^ 2) + p1 * a)) / A := by field_simp
    rw [this]; exact div_pos hq hApos
  linarith

end Work.Data.FR13Val
