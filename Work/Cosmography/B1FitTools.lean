import Checked.Cosmography.B1Truncation

/-!
# Tools for the B1 fit-level theorem: second-order certified enclosures of the ΛCDM distance integral

`J(w) = ∫_w^1 2/√(Ω + (1−Ω)v⁶) dv` is enclosed cell by cell: on each cell the integrand is bounded
below by the tangent of `1/√y` (any `c ≥ 0`) and above by its chord (`p² ≤ y ≤ q²` on the cell);
both bounds are polynomials in `v` (`y` is), integrated exactly. Unlike monotone Riemann sums the
error is second order in the cell size. Certificates are produced by
`runs/2026-11-04T0228Z/scripts/gen_fit.py`; Lean checks them.
-/

namespace Work.Cosmography.B1Fit

open Checked.Cosmography.B1 Set

lemma integral_poly6 (α β A B : ℝ) :
    ∫ v in α..β, (A - B * v ^ 6) = A * (β - α) - B * (β ^ 7 - α ^ 7) / 7 := by
  have hd : ∀ x ∈ uIcc α β, HasDerivAt (fun v : ℝ => A * v - B * v ^ 7 / 7) (A - B * x ^ 6) x := by
    intro x _
    have h := ((hasDerivAt_id' x).const_mul A).sub (((hasDerivAt_pow 7 x).const_mul B).div_const 7)
    exact h.congr_deriv (by push_cast; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (by apply Continuous.intervalIntegrable; fun_prop)]
  ring

lemma gL_intInt (Ω : ℝ) (hΩ₀ : 0 ≤ Ω) (hΩ₁ : Ω ≤ 1) (α β : ℝ) (hα : 0 < α) (hαβ : α ≤ β) :
    IntervalIntegrable (gL Ω) MeasureTheory.volume α β := by
  apply (gL_cont Ω hΩ₀ hΩ₁).mono _ |>.intervalIntegrable
  intro z hz; rw [uIcc_of_le hαβ] at hz; exact lt_of_lt_of_le hα hz.1

/-- Tangent cell bound. -/
lemma cell_lower (Ω c α β : ℝ) (hΩ₀ : 0 ≤ Ω) (hΩ₁ : Ω ≤ 1) (hα : 0 < α) (hαβ : α ≤ β)
    (hc : 0 ≤ c) :
    (β - α) * (3 * c - c ^ 3 * Ω) - c ^ 3 * (1 - Ω) * (β ^ 7 - α ^ 7) / 7
      ≤ ∫ v in α..β, gL Ω v := by
  have e := integral_poly6 α β (3 * c - c ^ 3 * Ω) (c ^ 3 * (1 - Ω))
  have hle : ∫ v in α..β, ((3 * c - c ^ 3 * Ω) - c ^ 3 * (1 - Ω) * v ^ 6)
      ≤ ∫ v in α..β, gL Ω v := by
    apply intervalIntegral.integral_mono_on hαβ
      (by apply Continuous.intervalIntegrable; fun_prop) (gL_intInt Ω hΩ₀ hΩ₁ α β hα hαβ)
    intro v hv
    have hv0 : 0 < v := lt_of_lt_of_le hα hv.1
    have hin := inner_pos Ω v hΩ₀ hΩ₁ hv0
    have := tangent_le _ c hin hc
    unfold gL; rw [div_eq_mul_one_div 2]; nlinarith
  rw [e] at hle; linarith

lemma y_mono_v (Ω u v : ℝ) (hΩ₁ : Ω ≤ 1) (hu : 0 ≤ u) (huv : u ≤ v) :
    Ω + (1 - Ω) * u ^ 6 ≤ Ω + (1 - Ω) * v ^ 6 := by
  have : u ^ 6 ≤ v ^ 6 := pow_le_pow_left₀ hu huv 6
  nlinarith [mul_le_mul_of_nonneg_left this (by linarith : 0 ≤ 1 - Ω)]

/-- Chord cell bound. -/
lemma cell_upper (Ω p q α β : ℝ) (hΩ₀ : 0 ≤ Ω) (hΩ₁ : Ω ≤ 1) (hα : 0 < α) (hαβ : α ≤ β)
    (hp : 0 < p) (hq : 0 < q) (h1 : p ^ 2 ≤ Ω + (1 - Ω) * α ^ 6)
    (h2 : Ω + (1 - Ω) * β ^ 6 ≤ q ^ 2) :
    ∫ v in α..β, gL Ω v ≤ 2 * (β - α) / p
      - 2 / (p * q * (p + q)) * ((β - α) * Ω + (1 - Ω) * (β ^ 7 - α ^ 7) / 7 - (β - α) * p ^ 2) := by
  set g := 2 / (p * q * (p + q)) with hg
  have e := integral_poly6 α β (2 / p - g * Ω + g * p ^ 2) (g * (1 - Ω))
  have hle : ∫ v in α..β, gL Ω v
      ≤ ∫ v in α..β, ((2 / p - g * Ω + g * p ^ 2) - g * (1 - Ω) * v ^ 6) := by
    apply intervalIntegral.integral_mono_on hαβ (gL_intInt Ω hΩ₀ hΩ₁ α β hα hαβ)
      (by apply Continuous.intervalIntegrable; fun_prop)
    intro v hv
    have hv0 : 0 < v := lt_of_lt_of_le hα hv.1
    have hy1 := le_trans h1 (y_mono_v Ω α v hΩ₁ hα.le hv.1)
    have hy2 := le_trans (y_mono_v Ω v β hΩ₁ hv0.le hv.2) h2
    have := le_secant _ p q hp hq hy1 hy2
    have eg : (Ω + (1 - Ω) * v ^ 6 - p ^ 2) / (p * q * (p + q))
        = g / 2 * (Ω + (1 - Ω) * v ^ 6 - p ^ 2) := by rw [hg]; field_simp
    rw [eg] at this
    have e2 : gL Ω v = 2 * (1 / √(Ω + (1 - Ω) * v ^ 6)) := by unfold gL; ring
    rw [e2]
    have h3 : 2 * (1 / √(Ω + (1 - Ω) * v ^ 6))
        ≤ 2 * (1 / p - g / 2 * (Ω + (1 - Ω) * v ^ 6 - p ^ 2)) := by linarith
    exact le_trans h3 (le_of_eq (by ring))
  rw [e] at hle; exact le_trans hle (le_of_eq (by ring))

/-- Summing tangent cells over the uniform grid `w + i h`. -/
lemma sum_lower (Ω : ℝ) (hΩ₀ : 0 ≤ Ω) (hΩ₁ : Ω ≤ 1) (w h : ℝ) (hw : 0 < w) (hh : 0 < h)
    (c : ℕ → ℝ) (hc : ∀ i, 0 ≤ c i) (N : ℕ) :
    ∑ i ∈ Finset.range N, (h * (3 * c i - c i ^ 3 * Ω)
        - c i ^ 3 * (1 - Ω) * ((w + (i + 1) * h) ^ 7 - (w + i * h) ^ 7) / 7)
      ≤ ∫ v in w..w + N * h, gL Ω v := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
    have hcell := cell_lower Ω (c n) (w + n * h) (w + (n + 1) * h) hΩ₀ hΩ₁ (by positivity)
      (by nlinarith) (hc n)
    have e1 : w + (n + 1) * h - (w + n * h) = h := by ring
    rw [e1] at hcell
    push_cast
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (gL_intInt Ω hΩ₀ hΩ₁ w (w + n * h) hw (by nlinarith))
      (gL_intInt Ω hΩ₀ hΩ₁ (w + n * h) (w + (n + 1) * h) (by positivity) (by nlinarith))]
    linarith

/-- Summing chord cells over the uniform grid `w + i h`. -/
lemma sum_upper (Ω : ℝ) (hΩ₀ : 0 ≤ Ω) (hΩ₁ : Ω ≤ 1) (w h : ℝ) (hw : 0 < w) (hh : 0 < h)
    (p q : ℕ → ℝ) (N : ℕ) (hp : ∀ i < N, 0 < p i) (hq : ∀ i < N, 0 < q i)
    (h1 : ∀ i < N, p i ^ 2 ≤ Ω + (1 - Ω) * (w + i * h) ^ 6)
    (h2 : ∀ i < N, Ω + (1 - Ω) * (w + (i + 1) * h) ^ 6 ≤ q i ^ 2) :
    ∫ v in w..w + N * h, gL Ω v ≤ ∑ i ∈ Finset.range N, (2 * h / p i
      - 2 / (p i * q i * (p i + q i)) * (h * Ω
        + (1 - Ω) * ((w + (i + 1) * h) ^ 7 - (w + i * h) ^ 7) / 7 - h * p i ^ 2)) := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
    have hcell := cell_upper Ω (p n) (q n) (w + n * h) (w + (n + 1) * h) hΩ₀ hΩ₁ (by positivity)
      (by nlinarith) (hp n (by omega)) (hq n (by omega)) (h1 n (by omega)) (h2 n (by omega))
    have e1 : w + (n + 1) * h - (w + n * h) = h := by ring
    rw [e1] at hcell
    have ih' := ih (fun i hi => hp i (by omega)) (fun i hi => hq i (by omega))
      (fun i hi => h1 i (by omega)) (fun i hi => h2 i (by omega))
    push_cast
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (gL_intInt Ω hΩ₀ hΩ₁ w (w + n * h) hw (by nlinarith))
      (gL_intInt Ω hΩ₀ hΩ₁ (w + n * h) (w + (n + 1) * h) (by positivity) (by nlinarith))]
    linarith

/-! ## Algebra of the fit condition -/

/-- The log-polynomial at the ΛCDM-implied coefficients, in `u = ln(1+z)` (divided by `ln 10`). -/
noncomputable def Qf (Ω u : ℝ) : ℝ := u + (3 / 2 - 3 / 4 * Ω) * u ^ 2 + (9 / 8 * Ω ^ 2 - 2 * Ω + 7 / 6) * u ^ 3

lemma Qf_mono (Ω u v : ℝ) (h1 : Ω ≤ 1) (hu : 0 ≤ u) (huv : u ≤ v) :
    Qf Ω u ≤ Qf Ω v := by
  have hA2 : 0 ≤ 3 / 2 - 3 / 4 * Ω := by linarith
  have hA3 : 0 ≤ 9 / 8 * Ω ^ 2 - 2 * Ω + 7 / 6 := by nlinarith [sq_nonneg (Ω - 8 / 9)]
  have h2 : u ^ 2 ≤ v ^ 2 := pow_le_pow_left₀ hu huv 2
  have h3 : u ^ 3 ≤ v ^ 3 := pow_le_pow_left₀ hu huv 3
  unfold Qf
  nlinarith [mul_le_mul_of_nonneg_left h2 hA2, mul_le_mul_of_nonneg_left h3 hA3]

/-- From two distance moduli each within `1/20` of a common offset `c`: the distance ratio
`(d_k/L_k)/(d_j/L_j)` exceeds `κ = 0.95499 < 10^(−1/50)`. -/
lemma ratio_step (dk dj Lk Lj c : ℝ) (hdk : 0 < dk) (hdj : 0 < dj) (hLk : 0 < Lk) (hLj : 0 < Lj)
    (hk : |5 * Real.logb 10 (dk / Lk) - c| ≤ 1 / 20)
    (hj : |5 * Real.logb 10 (dj / Lj) - c| ≤ 1 / 20) :
    95499 / 100000 * (dj * Lk) ≤ dk * Lj := by
  have hk' := (abs_le.1 hk).1
  have hj' := (abs_le.1 hj).2
  have hX : 0 < dk / Lk := div_pos hdk hLk
  have hY : 0 < dj / Lj := div_pos hdj hLj
  have hlog : -(1 / 50) ≤ Real.logb 10 ((dk / Lk) / (dj / Lj)) := by
    rw [Real.logb_div hX.ne' hY.ne']; linarith
  have hR : 0 < (dk / Lk) / (dj / Lj) := div_pos hX hY
  have hκ : (95499 / 100000 : ℝ) ≤ (dk / Lk) / (dj / Lj) := by
    by_contra hcon
    rw [not_le] at hcon
    have h1 : Real.logb 10 ((dk / Lk) / (dj / Lj)) < Real.logb 10 (95499 / 100000) :=
      Real.logb_lt_logb (by norm_num) hR hcon
    have h2 : Real.logb 10 (95499 / 100000 : ℝ) < -(1 / 50) := by
      have hl10 : 0 < Real.log 10 := Real.log_pos (by norm_num)
      rw [Real.logb, div_lt_iff₀ hl10]
      have hp : Real.log ((95499 / 100000 : ℝ) ^ 50) < Real.log (1 / 10) :=
        Real.log_lt_log (by positivity) (by norm_num)
      rw [Real.log_pow, one_div, Real.log_inv] at hp
      push_cast at hp; linarith
    linarith
  have e : (dk / Lk) / (dj / Lj) = (dk * Lj) / (dj * Lk) := by field_simp
  rw [e, le_div_iff₀ (by positivity)] at hκ
  linarith

/-- Clearing the common factors `1/H₀`, `1/H` and the source factor `(1+z_j)`. -/
lemma ratio_clean (κ sj sk H₀ H Jj Jk Pk Pj r : ℝ) (hsj : 0 < sj) (hH₀ : 0 < H₀) (hH : 0 < H)
    (hsk : sk = r * sj)
    (h : κ * ((sj / H₀ * Jj) * (Pk / H)) ≤ (sk / H₀ * Jk) * (Pj / H)) :
    κ * Jj * Pk ≤ r * Jk * Pj := by
  rw [hsk] at h
  have hc : 0 < sj / (H₀ * H) := by positivity
  have e1 : κ * ((sj / H₀ * Jj) * (Pk / H)) = sj / (H₀ * H) * (κ * Jj * Pk) := by
    field_simp
  have e2 : (r * sj / H₀ * Jk) * (Pj / H) = sj / (H₀ * H) * (r * Jk * Pj) := by
    field_simp
  rw [e1, e2] at h
  exact le_of_mul_le_mul_left h hc

/-- One matching constraint: enclosures `Lj ≤ Jj`, `Jk ≤ Uk` and `r Uk ≤ ρ κ Lj` turn
`κ Jj Pk ≤ r Jk Pj` into `Pk ≤ ρ Pj`. -/
lemma constr (κ r ρ Jj Jk Pk Pj Lj Uk : ℝ) (hκ : 0 < κ) (hr : 0 ≤ r) (hL : 0 < Lj)
    (hPk : 0 < Pk) (hPj : 0 < Pj) (h : κ * Jj * Pk ≤ r * Jk * Pj) (hLj : Lj ≤ Jj)
    (hUk : Jk ≤ Uk) (hρ : r * Uk ≤ ρ * (κ * Lj)) : Pk ≤ ρ * Pj := by
  have e1 : κ * Lj * Pk ≤ κ * Jj * Pk :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hLj hκ.le) hPk.le
  have e2 : r * Jk * Pj ≤ r * Uk * Pj :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hUk hr) hPj.le
  have e3 : r * Uk * Pj ≤ ρ * (κ * Lj) * Pj := mul_le_mul_of_nonneg_right hρ hPj.le
  have h4 : (κ * Lj) * Pk ≤ (κ * Lj) * (ρ * Pj) := by nlinarith
  exact le_of_mul_le_mul_left h4 (by positivity)

lemma log_ten_ge : (10 * 0.6931471803 - 24 / 1000) / 3 ≤ Real.log 10 := by
  have h1 := Real.one_sub_inv_le_log_of_pos (show (0:ℝ) < 1000 / 1024 by norm_num)
  have h2 : Real.log (1000 / 1024) = 3 * Real.log 10 - 10 * Real.log 2 := by
    rw [Real.log_div (by norm_num) (by norm_num),
      show (1000:ℝ) = 10 ^ 3 by norm_num, show (1024:ℝ) = 2 ^ 10 by norm_num,
      Real.log_pow, Real.log_pow]; push_cast; ring
  rw [h2] at h1
  have h3 : ((1000:ℝ) / 1024)⁻¹ = 1024 / 1000 := by norm_num
  rw [h3] at h1
  linarith [Real.log_two_gt_d9]

/-- Back to the papers' coefficients. -/
lemma conclude (Ω a₂ a₃ e₂ e₃ : ℝ)
    (he₂ : e₂ = (a₂ / Real.log 10 - (3 / 2 - 3 / 4 * Ω)) * Real.log 2 ^ 2)
    (he₃ : e₃ = (a₃ / Real.log 10 ^ 2 - (9 / 8 * Ω ^ 2 - 2 * Ω + 7 / 6)) * Real.log 2 ^ 3)
    (h : (1044 / 10000 : ℝ) ≤ 20 / 3 * e₃ - e₂) :
    a₂ - lusA2 Ω + 1 / 2 < 20 / 3 * Real.logb 10 2 * (a₃ - lusA3 Ω) := by
  set l := Real.log 10 with hl
  set ℓ := Real.log 2 with hℓ
  have hl0 : 0 < l := Real.log_pos (by norm_num)
  have hℓ0 : 0 < ℓ := Real.log_pos (by norm_num)
  have hlb := log_ten_ge
  have hℓ1 : ℓ < 0.6931471808 := Real.log_two_lt_d9
  -- ℓ² < 2 l M
  have hsmall : ℓ ^ 2 < 2 * l * (1044 / 10000) := by
    have : ℓ ^ 2 < 0.6931471808 ^ 2 := by nlinarith
    nlinarith
  have key : 20 / 3 * Real.logb 10 2 * (a₃ - lusA3 Ω) - (a₂ - lusA2 Ω)
      = l / ℓ ^ 2 * (20 / 3 * e₃ - e₂) := by
    rw [he₂, he₃]; unfold lusA2 lusA3 Real.logb; rw [← hl, ← hℓ]; field_simp
  have hpos : 1 / 2 < l / ℓ ^ 2 * (20 / 3 * e₃ - e₂) := by
    have h2 : l / ℓ ^ 2 * (1044 / 10000) ≤ l / ℓ ^ 2 * (20 / 3 * e₃ - e₂) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    have h3 : 1 / 2 < l / ℓ ^ 2 * (1044 / 10000) := by
      rw [div_mul_eq_mul_div, lt_div_iff₀ (by positivity)]; nlinarith
    linarith
  linarith

end Work.Cosmography.B1Fit
