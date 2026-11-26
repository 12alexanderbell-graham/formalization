import Mathlib

/-! Target 2: certified decimals of the Montgomery–Taylor constant. With θ = 1/√2,
c_MT⁻¹ = 1/2 + cot θ/√2 (paper), equal to 1/cMT for the frozen closed form, and
2 − c_MT⁻¹ ≥ 0.672 (the announced "67.2%"). Taylor polynomials of cos, sin at θ to degree 7
with Mathlib's `Complex.exp_bound` (n = 8, error ≤ θ⁸·9/(8!·8) < 2·10⁻⁶). -/

namespace ExternalT2.Dec
open Complex

noncomputable def θ : ℝ := 1 / Real.sqrt 2

lemma θ_sq : θ ^ 2 = 1 / 2 := by
  unfold θ; rw [div_pow, Real.sq_sqrt (by norm_num)]; norm_num

lemma θ_pos : 0 < θ := by unfold θ; positivity

lemma θ_le_one : θ ≤ 1 := by
  unfold θ; rw [div_le_one (by positivity)]
  rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num

lemma θ_bounds : (70710 / 100000 : ℝ) < θ ∧ θ < 70711 / 100000 := by
  have h := θ_sq; have hp := θ_pos
  constructor <;> nlinarith

/-- The degree-7 Taylor sum of `exp (θ I)`, split into real and imaginary parts. -/
lemma taylor_sum : ∑ m ∈ Finset.range 8, ((θ : ℂ) * I) ^ m / (m.factorial : ℂ) =
    ((1 - θ ^ 2 / 2 + θ ^ 4 / 24 - θ ^ 6 / 720 : ℝ) : ℂ) +
      ((θ - θ ^ 3 / 6 + θ ^ 5 / 120 - θ ^ 7 / 5040 : ℝ) : ℂ) * I := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
  push_cast
  ring_nf
  simp only [I_sq, I_pow_four, show I ^ 3 = -I by rw [pow_succ, I_sq]; ring,
    show I ^ 5 = I by rw [pow_succ, I_pow_four, one_mul],
    show I ^ 6 = -1 by rw [show (6:ℕ) = 4 + 2 by rfl, pow_add, I_pow_four, I_sq]; ring,
    show I ^ 7 = -I by rw [show (7:ℕ) = 4 + 3 by rfl, pow_add, I_pow_four, pow_succ, I_sq]; ring]
  ring

lemma err_bound : ‖Complex.exp ((θ : ℂ) * I) -
    ∑ m ∈ Finset.range 8, ((θ : ℂ) * I) ^ m / (m.factorial : ℂ)‖ ≤ 1 / 500000 := by
  have hn : ‖(θ : ℂ) * I‖ = θ := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos θ_pos]
  have h := Complex.exp_bound (x := (θ : ℂ) * I) (by rw [hn]; exact θ_le_one) (n := 8) (by norm_num)
  rw [hn] at h
  refine h.trans ?_
  have h8 : θ ^ 8 = 1 / 16 := by rw [show (8:ℕ) = 2 * 4 by rfl, pow_mul, θ_sq]; norm_num
  rw [h8]; simp [Nat.factorial]; norm_num

lemma cos_bounds : |Real.cos θ - (1 - θ ^ 2 / 2 + θ ^ 4 / 24 - θ ^ 6 / 720)| ≤ 1 / 500000 := by
  have h := err_bound
  rw [taylor_sum] at h
  have hre := Complex.abs_re_le_norm (Complex.exp ((θ : ℂ) * I) -
    (((1 - θ ^ 2 / 2 + θ ^ 4 / 24 - θ ^ 6 / 720 : ℝ) : ℂ) +
      ((θ - θ ^ 3 / 6 + θ ^ 5 / 120 - θ ^ 7 / 5040 : ℝ) : ℂ) * I))
  simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    Complex.I_im, Complex.ofReal_im, mul_zero, mul_one, sub_zero, add_zero,
    Complex.exp_ofReal_mul_I_re] at hre
  linarith

lemma sin_bounds : |Real.sin θ - (θ - θ ^ 3 / 6 + θ ^ 5 / 120 - θ ^ 7 / 5040)| ≤ 1 / 500000 := by
  have h := err_bound
  rw [taylor_sum] at h
  have him := Complex.abs_im_le_norm (Complex.exp ((θ : ℂ) * I) -
    (((1 - θ ^ 2 / 2 + θ ^ 4 / 24 - θ ^ 6 / 720 : ℝ) : ℂ) +
      ((θ - θ ^ 3 / 6 + θ ^ 5 / 120 - θ ^ 7 / 5040 : ℝ) : ℂ) * I))
  simp only [Complex.sub_im, Complex.add_im, Complex.ofReal_re, Complex.mul_im, Complex.I_re,
    Complex.I_im, Complex.ofReal_im, mul_zero, mul_one, zero_mul, add_zero, zero_add,
    Complex.exp_ofReal_mul_I_im] at him
  linarith

/-- `cot θ ≤ 1.1709`. -/
lemma cot_le : Real.cot θ ≤ 117035 / 100000 := by
  have hc := cos_bounds; have hs := sin_bounds
  have h2 := θ_sq; have hb := θ_bounds
  have e3 : θ ^ 3 = θ / 2 := by rw [pow_succ, h2]; ring
  have e4 : θ ^ 4 = 1 / 4 := by rw [show θ ^ 4 = (θ ^ 2) ^ 2 by ring, h2]; norm_num
  have e5 : θ ^ 5 = θ / 4 := by rw [pow_succ, e4]; ring
  have e6 : θ ^ 6 = 1 / 8 := by rw [show θ ^ 6 = (θ ^ 2) ^ 3 by ring, h2]; norm_num
  have e7 : θ ^ 7 = θ / 8 := by rw [pow_succ, e6]; ring
  rw [h2, e4, e6] at hc; rw [e3, e5, e7] at hs
  rw [abs_le] at hc hs
  have hsin : 0 < Real.sin θ := by nlinarith
  rw [Real.cot_eq_cos_div_sin, div_le_iff₀ hsin]
  nlinarith

/-- The paper's `c_MT⁻¹ = 1/2 + cot θ/√2` is the reciprocal of the frozen closed form
`cMT = √2 tan θ/(1 + θ tan θ)`. -/
lemma inv_eq : (Real.sqrt 2 * Real.tan θ / (1 + θ * Real.tan θ))⁻¹ =
    1 / 2 + θ * Real.cot θ := by
  have hb := θ_bounds
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi θ_pos (by linarith [Real.pi_gt_three])
  have hc : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_gt_three], by linarith [Real.pi_gt_three]⟩
  have h2 : Real.sqrt 2 = 2 * θ := by
    unfold θ; field_simp; rw [Real.sq_sqrt (by norm_num)]
  rw [Real.tan_eq_sin_div_cos, Real.cot_eq_cos_div_sin, h2]
  have hθ := θ_sq
  field_simp
  rw [div_eq_iff θ_pos.ne']
  linear_combination (-2 * Real.cos θ) * hθ

theorem headline_decimal : (672 / 1000 : ℝ) ≤ 2 - 1 / (Real.sqrt 2 * Real.tan (1 / Real.sqrt 2) /
    (1 + 1 / Real.sqrt 2 * Real.tan (1 / Real.sqrt 2))) := by
  have h := inv_eq; have hc := cot_le; have hb := θ_bounds
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi θ_pos (by linarith [Real.pi_gt_three])
  have hco : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_gt_three], by linarith [Real.pi_gt_three]⟩
  have hcot : 0 < Real.cot θ := by rw [Real.cot_eq_cos_div_sin]; positivity
  have key : θ * Real.cot θ ≤ 70711 / 100000 * (117035 / 100000) := by
    apply mul_le_mul hb.2.le hc hcot.le (by norm_num)
  show (672 / 1000 : ℝ) ≤ 2 - 1 / (Real.sqrt 2 * Real.tan θ / (1 + θ * Real.tan θ))
  rw [one_div (Real.sqrt 2 * _ / _), h]
  linarith

end ExternalT2.Dec
#print axioms ExternalT2.Dec.headline_decimal
