import Mathlib

/-!
# Tools for certified chi-square fits of H(z) tables (proof tools for `Work.Data.FR13`)

Generic over the table. `chiSq`, `margChi` restate the frozen definitions of `Work.Data.FR13`
(definitionally equal; this file is imported by it, so it cannot import it).
-/

namespace Work.Data.FR13Tools
open MeasureTheory Real

/-- Same body as `Work.Data.FR13.chiSqHz`. -/
noncomputable def chiSq {n : ℕ} (tbl : Fin n → ℝ × ℝ × ℝ) (H₀ Ω : ℝ) : ℝ :=
  ∑ i, ((H₀ * √(Ω * (1 + (tbl i).1) ^ 3 + 1 - Ω) - (tbl i).2.1) / (tbl i).2.2) ^ 2

/-- Same body as `Work.Data.FR13.margChiSq`. -/
noncomputable def margChi {n : ℕ} (tbl : Fin n → ℝ × ℝ × ℝ) (Hbar σ Ω : ℝ) : ℝ :=
  -2 * Real.log (∫ H₀ : ℝ, Real.exp (-chiSq tbl H₀ Ω / 2) *
    (Real.exp (-(H₀ - Hbar) ^ 2 / (2 * σ ^ 2)) / √(2 * Real.pi * σ ^ 2)))

/-- E² of row i. -/
noncomputable def esq {n : ℕ} (tbl : Fin n → ℝ × ℝ × ℝ) (Ω : ℝ) (i : Fin n) : ℝ :=
  Ω * (1 + (tbl i).1) ^ 3 + 1 - Ω

noncomputable def S2 {n : ℕ} (tbl : Fin n → ℝ × ℝ × ℝ) (Ω : ℝ) : ℝ :=
  ∑ i, (√(esq tbl Ω i)) ^ 2 / (tbl i).2.2 ^ 2
noncomputable def S1 {n : ℕ} (tbl : Fin n → ℝ × ℝ × ℝ) (Ω : ℝ) : ℝ :=
  ∑ i, (tbl i).2.1 * √(esq tbl Ω i) / (tbl i).2.2 ^ 2
noncomputable def S0 {n : ℕ} (tbl : Fin n → ℝ × ℝ × ℝ) : ℝ :=
  ∑ i, (tbl i).2.1 ^ 2 / (tbl i).2.2 ^ 2

theorem chiSq_expand {n : ℕ} (tbl : Fin n → ℝ × ℝ × ℝ) (H Ω : ℝ) :
    chiSq tbl H Ω = H ^ 2 * S2 tbl Ω - 2 * H * S1 tbl Ω + S0 tbl := by
  unfold chiSq S2 S1 S0 esq
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem gauss_shift (a b c : ℝ) (ha : 0 < a) :
    ∫ x : ℝ, exp (-(a * x ^ 2 - 2 * b * x + c) / 2) = √(π / (a / 2)) * exp (-(c - b ^ 2 / a) / 2) := by
  have h : ∀ x : ℝ, exp (-(a * x ^ 2 - 2 * b * x + c) / 2)
      = exp (-(a / 2) * (x - b / a) ^ 2) * exp (-(c - b ^ 2 / a) / 2) := by
    intro x; rw [← exp_add]; congr 1; field_simp; ring
  simp_rw [h]
  rw [integral_mul_const, integral_sub_right_eq_self (fun x => exp (-(a / 2) * x ^ 2)) (b / a),
    integral_gaussian]

/-- Closed form of the marginalised chi-square. -/
theorem margChi_closed {n : ℕ} (tbl : Fin n → ℝ × ℝ × ℝ) (Hbar σ Ω : ℝ) (hσ : 0 < σ) :
    margChi tbl Hbar σ Ω = (S0 tbl + Hbar ^ 2 / σ ^ 2)
      - (S1 tbl Ω + Hbar / σ ^ 2) ^ 2 / (S2 tbl Ω + 1 / σ ^ 2)
      + Real.log (σ ^ 2 * (S2 tbl Ω + 1 / σ ^ 2)) := by
  set A := S2 tbl Ω + 1 / σ ^ 2 with hA
  set B := S1 tbl Ω + Hbar / σ ^ 2 with hB
  set C := S0 tbl + Hbar ^ 2 / σ ^ 2 with hC
  have hS2 : 0 ≤ S2 tbl Ω := Finset.sum_nonneg fun i _ => div_nonneg (sq_nonneg _) (sq_nonneg _)
  have hσ2 : 0 < σ ^ 2 := by positivity
  have hApos : 0 < A := by rw [hA]; positivity
  have hint : ∀ H : ℝ, Real.exp (-chiSq tbl H Ω / 2) *
      (Real.exp (-(H - Hbar) ^ 2 / (2 * σ ^ 2)) / √(2 * Real.pi * σ ^ 2))
      = Real.exp (-(A * H ^ 2 - 2 * B * H + C) / 2) / √(2 * Real.pi * σ ^ 2) := by
    intro H
    rw [mul_div_assoc', ← Real.exp_add, chiSq_expand]
    congr 2
    rw [hA, hB, hC]; field_simp; ring
  unfold margChi
  simp_rw [hint]
  rw [integral_div, gauss_shift A B C hApos]
  have hpi : 0 < Real.pi := Real.pi_pos
  have h1 : 0 < √(Real.pi / (A / 2)) := Real.sqrt_pos.2 (by positivity)
  have h2 : 0 < √(2 * Real.pi * σ ^ 2) := Real.sqrt_pos.2 (by positivity)
  rw [Real.log_div (by positivity) h2.ne', Real.log_mul h1.ne' (Real.exp_pos _).ne', Real.log_exp,
    Real.log_sqrt (by positivity), Real.log_sqrt (by positivity),
    Real.log_div hpi.ne' (by positivity), Real.log_div hApos.ne' two_ne_zero,
    Real.log_mul (by positivity) hσ2.ne', Real.log_mul (by positivity) hpi.ne',
    Real.log_mul hσ2.ne' hApos.ne']
  ring

/-! ### Square-root bounds without square roots -/

theorem sqrt_le_tangent (y s : ℝ) (hy : 0 ≤ y) (hs : 0 < s) : √y ≤ (y + s ^ 2) / (2 * s) := by
  rw [le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg (√y - s), Real.sq_sqrt hy, Real.sqrt_nonneg y]

theorem sqrt_ge_harm (y s : ℝ) (hy : 0 ≤ y) (hs : 0 < s) : 2 * s * y / (y + s ^ 2) ≤ √y := by
  rw [div_le_iff₀ (by positivity)]
  nlinarith [sq_nonneg (√y - s), Real.sq_sqrt hy, Real.sqrt_nonneg y, mul_nonneg (Real.sqrt_nonneg y) (sq_nonneg (√y - s))]

/-- Concave quadratic positive at both ends of an interval is positive inside. -/
theorem quad_pos (K A0 A1 β0 β1 Ar a b Ω : ℝ) (ha : a ≤ Ω) (hb : Ω ≤ b)
    (hqa : 0 < K * (A0 + A1 * a) - (β0 + β1 * a) ^ 2 - Ar)
    (hqb : 0 < K * (A0 + A1 * b) - (β0 + β1 * b) ^ 2 - Ar) :
    0 < K * (A0 + A1 * Ω) - (β0 + β1 * Ω) ^ 2 - Ar := by
  rcases eq_or_lt_of_le (ha.trans hb) with hab | hab
  · have : Ω = a := le_antisymm (hab ▸ hb) ha
    rw [this]; exact hqa
  have key : (b - a) * (K * (A0 + A1 * Ω) - (β0 + β1 * Ω) ^ 2 - Ar)
      = (b - Ω) * (K * (A0 + A1 * a) - (β0 + β1 * a) ^ 2 - Ar)
        + (Ω - a) * (K * (A0 + A1 * b) - (β0 + β1 * b) ^ 2 - Ar)
        + β1 ^ 2 * (Ω - a) * (b - Ω) * (b - a) := by ring
  have hba : 0 < b - a := by linarith
  have : 0 < (b - a) * (K * (A0 + A1 * Ω) - (β0 + β1 * Ω) ^ 2 - Ar) := by
    rw [key]
    rcases eq_or_lt_of_le hb with h | h
    · subst h; nlinarith [mul_nonneg (sq_nonneg β1) (mul_nonneg (sub_nonneg.2 ha) (sub_nonneg.2 hb))]
    · have : 0 < b - Ω := by linarith
      nlinarith [mul_nonneg (sub_nonneg.2 ha) hqb.le,
        mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg β1) (sub_nonneg.2 ha)) (sub_nonneg.2 hb)) hba.le]
  exact pos_of_mul_pos_right this hba.le

/-- The comparison step: if the profile parts are bounded as stated, M(Ω) > M(Ωr). -/
theorem compare (C A Ar B Br Blo β σ : ℝ) (hσ : 0 < σ) (hA : 0 < A) (hAr : 0 < Ar)
    (hB0 : 0 ≤ B) (hBβ : B ≤ β) (hlo0 : 0 ≤ Blo) (hlo : Blo ≤ Br)
    (hq : 0 < (Blo ^ 2 / Ar + 1) * A - β ^ 2 - Ar) :
    C - Br ^ 2 / Ar + Real.log (σ ^ 2 * Ar) < C - B ^ 2 / A + Real.log (σ ^ 2 * A) := by
  have hσ2 : 0 < σ ^ 2 := by positivity
  have hlog : Real.log (σ ^ 2 * A) - Real.log (σ ^ 2 * Ar) ≥ 1 - Ar / A := by
    rw [← Real.log_div (by positivity) (by positivity)]
    have : σ ^ 2 * A / (σ ^ 2 * Ar) = A / Ar := by field_simp
    rw [this]
    have h := Real.one_sub_inv_le_log_of_pos (div_pos hA hAr)
    rw [inv_div] at h; linarith
  have hB2 : B ^ 2 ≤ β ^ 2 := pow_le_pow_left₀ hB0 hBβ 2
  have hBr2 : Blo ^ 2 ≤ Br ^ 2 := pow_le_pow_left₀ hlo0 hlo 2
  have h1 : B ^ 2 / A ≤ β ^ 2 / A := div_le_div_of_nonneg_right hB2 hA.le
  have h2 : Blo ^ 2 / Ar ≤ Br ^ 2 / Ar := div_le_div_of_nonneg_right hBr2 hAr.le
  have h3 : 0 < Blo ^ 2 / Ar - β ^ 2 / A + 1 - Ar / A := by
    have : Blo ^ 2 / Ar - β ^ 2 / A + 1 - Ar / A
        = ((Blo ^ 2 / Ar + 1) * A - β ^ 2 - Ar) / A := by field_simp; ring
    rw [this]; exact div_pos hq hA
  linarith


/-! ### Table-level bounds -/

noncomputable def T0 {n : ℕ} (tbl : Fin n → ℝ × ℝ × ℝ) (s : Fin n → ℝ) : ℝ :=
  ∑ i, (tbl i).2.1 * (1 + s i ^ 2) / (2 * s i * (tbl i).2.2 ^ 2)
noncomputable def T1 {n : ℕ} (tbl : Fin n → ℝ × ℝ × ℝ) (s : Fin n → ℝ) : ℝ :=
  ∑ i, (tbl i).2.1 * ((1 + (tbl i).1) ^ 3 - 1) / (2 * s i * (tbl i).2.2 ^ 2)
noncomputable def Lsum {n : ℕ} (tbl : Fin n → ℝ × ℝ × ℝ) (s : Fin n → ℝ) (Ω : ℝ) : ℝ :=
  ∑ i, (tbl i).2.1 * (2 * s i * (Ω * (1 + (tbl i).1) ^ 3 + 1 - Ω)
    / ((Ω * (1 + (tbl i).1) ^ 3 + 1 - Ω) + s i ^ 2)) / (tbl i).2.2 ^ 2
noncomputable def P0 {n : ℕ} (tbl : Fin n → ℝ × ℝ × ℝ) : ℝ := ∑ i, 1 / (tbl i).2.2 ^ 2
noncomputable def P1 {n : ℕ} (tbl : Fin n → ℝ × ℝ × ℝ) : ℝ :=
  ∑ i, ((1 + (tbl i).1) ^ 3 - 1) / (tbl i).2.2 ^ 2

theorem esq_nonneg {n : ℕ} (tbl : Fin n → ℝ × ℝ × ℝ) (hz : ∀ i, 0 ≤ (tbl i).1) {Ω : ℝ}
    (h0 : 0 ≤ Ω) (h1 : Ω ≤ 1) (i : Fin n) : 0 ≤ esq tbl Ω i := by
  unfold esq
  have : 1 ≤ (1 + (tbl i).1) ^ 3 := one_le_pow₀ (by linarith [hz i])
  nlinarith

theorem S2_lin {n : ℕ} (tbl : Fin n → ℝ × ℝ × ℝ) (hz : ∀ i, 0 ≤ (tbl i).1) {Ω : ℝ}
    (h0 : 0 ≤ Ω) (h1 : Ω ≤ 1) : S2 tbl Ω = P0 tbl + P1 tbl * Ω := by
  unfold S2 P0 P1
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Real.sq_sqrt (esq_nonneg tbl hz h0 h1 i)]
  unfold esq; ring

theorem S1_le {n : ℕ} (tbl : Fin n → ℝ × ℝ × ℝ) (hz : ∀ i, 0 ≤ (tbl i).1)
    (hh : ∀ i, 0 ≤ (tbl i).2.1) (s : Fin n → ℝ) (hs : ∀ i, 0 < s i) {Ω : ℝ}
    (h0 : 0 ≤ Ω) (h1 : Ω ≤ 1) : S1 tbl Ω ≤ Ω * T1 tbl s + T0 tbl s := by
  unfold S1 T1 T0
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  have hsq := sqrt_le_tangent (esq tbl Ω i) (s i) (esq_nonneg tbl hz h0 h1 i) (hs i)
  have h2 : (tbl i).2.1 * √(esq tbl Ω i) / (tbl i).2.2 ^ 2
      ≤ (tbl i).2.1 * ((esq tbl Ω i + s i ^ 2) / (2 * s i)) / (tbl i).2.2 ^ 2 :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsq (hh i)) (sq_nonneg _)
  refine h2.trans (le_of_eq ?_)
  have := (hs i).ne'
  unfold esq
  field_simp
  ring

theorem S1_ge {n : ℕ} (tbl : Fin n → ℝ × ℝ × ℝ) (hz : ∀ i, 0 ≤ (tbl i).1)
    (hh : ∀ i, 0 ≤ (tbl i).2.1) (s : Fin n → ℝ) (hs : ∀ i, 0 < s i) {Ω : ℝ}
    (h0 : 0 ≤ Ω) (h1 : Ω ≤ 1) : Lsum tbl s Ω ≤ S1 tbl Ω := by
  unfold S1 Lsum
  refine Finset.sum_le_sum fun i _ => ?_
  have hsq := sqrt_ge_harm (esq tbl Ω i) (s i) (esq_nonneg tbl hz h0 h1 i) (hs i)
  unfold esq at hsq ⊢
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsq (hh i)) (sq_nonneg _)

theorem S1_nonneg {n : ℕ} (tbl : Fin n → ℝ × ℝ × ℝ) (hh : ∀ i, 0 ≤ (tbl i).2.1) (Ω : ℝ) :
    0 ≤ S1 tbl Ω :=
  Finset.sum_nonneg fun i _ =>
    div_nonneg (mul_nonneg (hh i) (Real.sqrt_nonneg _)) (sq_nonneg _)

/-- One group of the certificate: every Ω in [a, b] has a larger marginalised chi-square
than the reference point Ωr. All hypotheses after `hT1` are rational checks. -/
theorem group_ok {n : ℕ} (tbl : Fin n → ℝ × ℝ × ℝ) (hz : ∀ i, 0 ≤ (tbl i).1)
    (hh : ∀ i, 0 ≤ (tbl i).2.1) (Hb σ Ωr blo p0 p1 β0 β1 a b : ℝ) (s sR : Fin n → ℝ)
    (hσ : 0 < σ) (hHb : 0 ≤ Hb) (hP0 : P0 tbl = p0) (hP1 : P1 tbl = p1)
    (hs : ∀ i, 0 < s i) (hsR : ∀ i, 0 < sR i)
    (hr0 : 0 ≤ Ωr) (hr1 : Ωr ≤ 1) (ha0 : 0 ≤ a) (hb1 : b ≤ 1)
    (hT0 : T0 tbl s ≤ β0) (hT1 : T1 tbl s ≤ β1) (hlo : blo ≤ Lsum tbl sR Ωr) (hblo : 0 ≤ blo)
    (hqa : 0 < ((blo + Hb / σ ^ 2) ^ 2 / (p0 + 1 / σ ^ 2 + p1 * Ωr) + 1) * ((p0 + 1 / σ ^ 2) + p1 * a)
      - ((β0 + Hb / σ ^ 2) + β1 * a) ^ 2 - (p0 + 1 / σ ^ 2 + p1 * Ωr))
    (hqb : 0 < ((blo + Hb / σ ^ 2) ^ 2 / (p0 + 1 / σ ^ 2 + p1 * Ωr) + 1) * ((p0 + 1 / σ ^ 2) + p1 * b)
      - ((β0 + Hb / σ ^ 2) + β1 * b) ^ 2 - (p0 + 1 / σ ^ 2 + p1 * Ωr))
    (Ω : ℝ) (ha : a ≤ Ω) (hb : Ω ≤ b) :
    margChi tbl Hb σ Ωr < margChi tbl Hb σ Ω := by
  have h0 : 0 ≤ Ω := ha0.trans ha
  have h1 : Ω ≤ 1 := hb.trans hb1
  rw [margChi_closed _ _ _ _ hσ, margChi_closed _ _ _ _ hσ, S2_lin tbl hz h0 h1, S2_lin tbl hz hr0 hr1,
    hP0, hP1]
  have hσ2 : 0 < σ ^ 2 := by positivity
  have hP0n : 0 ≤ p0 := hP0 ▸ Finset.sum_nonneg fun i _ => div_nonneg zero_le_one (sq_nonneg _)
  have hP1n : 0 ≤ p1 := hP1 ▸ Finset.sum_nonneg fun i _ => div_nonneg (by
    have : 1 ≤ (1 + (tbl i).1) ^ 3 := one_le_pow₀ (by linarith [hz i])
    linarith) (sq_nonneg _)
  have hq := quad_pos ((blo + Hb / σ ^ 2) ^ 2 / (p0 + 1 / σ ^ 2 + p1 * Ωr) + 1) (p0 + 1 / σ ^ 2) p1
    (β0 + Hb / σ ^ 2) β1 (p0 + 1 / σ ^ 2 + p1 * Ωr) a b Ω ha hb hqa hqb
  have hS1 := S1_le tbl hz hh s hs h0 h1
  have hβ : S1 tbl Ω + Hb / σ ^ 2 ≤ (β0 + Hb / σ ^ 2) + β1 * Ω := by nlinarith
  have hL := S1_ge tbl hz hh sR hsR hr0 hr1
  refine compare _ (p0 + p1 * Ω + 1 / σ ^ 2) (p0 + p1 * Ωr + 1 / σ ^ 2) (S1 tbl Ω + Hb / σ ^ 2)
    (S1 tbl Ωr + Hb / σ ^ 2) (blo + Hb / σ ^ 2) ((β0 + Hb / σ ^ 2) + β1 * Ω) σ hσ (by positivity)
    (by positivity) (by have := S1_nonneg tbl hh Ω; positivity) hβ (by positivity) (by linarith) ?_
  have e1 : p0 + p1 * Ωr + 1 / σ ^ 2 = p0 + 1 / σ ^ 2 + p1 * Ωr := by ring
  have e2 : p0 + p1 * Ω + 1 / σ ^ 2 = (p0 + 1 / σ ^ 2) + p1 * Ω := by ring
  rw [e1, e2]; exact hq

end Work.Data.FR13Tools
