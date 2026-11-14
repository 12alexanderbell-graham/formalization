/-- The mass window at the second maximum from the window of u (v = 2u there). -/
theorem win_M {M U : ℝ} (hM : M ^ 2 * (4 * Real.pi) = 8 * U ^ 4) (hMpos : 0 < M)
    (u1 : 1020324 / 1000000 ≤ U) (u2 : U ≤ 1020415 / 1000000) : 0.8306 ≤ M ∧ M ≤ 0.8308 := by
  have pil := Real.pi_gt_d20
  have pih := Real.pi_lt_d20
  have v4l : (1020324 / 1000000 : ℝ) ^ 4 ≤ U ^ 4 := pow_le_pow_left₀ (by norm_num) u1 4
  have v4h : U ^ 4 ≤ (1020415 / 1000000 : ℝ) ^ 4 := pow_le_pow_left₀ (by linarith) u2 4
  constructor
  · by_contra hc
    push_neg at hc
    have h2 : M ^ 2 < 0.8306 ^ 2 := pow_lt_pow_left₀ hc hMpos.le (by norm_num)
    have h3 : M ^ 2 * (4 * Real.pi) < 0.8306 ^ 2 * (4 * Real.pi) :=
      mul_lt_mul_of_pos_right h2 (by positivity)
    nlinarith
  · by_contra hc
    push_neg at hc
    have h2 : (0.8308 : ℝ) ^ 2 < M ^ 2 := pow_lt_pow_left₀ hc (by norm_num) (by norm_num)
    have h3 : 0.8308 ^ 2 * (4 * Real.pi) < M ^ 2 * (4 * Real.pi) :=
      mul_lt_mul_of_pos_right h2 (by positivity)
    nlinarith

/-- The contrast window at the second maximum. -/
theorem win_C {ξ U : ℝ} (hU0 : 0 < U) (hξ1 : 14671 / 20 ≤ ξ) (hξ2 : ξ ≤ 73399 / 100)
    (u1 : 1020324 / 1000000 ≤ U) (u2 : U ≤ 1020415 / 1000000) :
    258300 ≤ ξ ^ 2 / (2 * U ^ 2) ∧ ξ ^ 2 / (2 * U ^ 2) ≤ 258800 := by
  constructor
  · rw [le_div_iff₀ (by positivity)]
    have : (1020415 / 1000000 : ℝ) ^ 2 ≥ U ^ 2 := pow_le_pow_left₀ hU0.le u2 2
    nlinarith
  · rw [div_le_iff₀ (by positivity)]
    have : (1020324 / 1000000 : ℝ) ^ 2 ≤ U ^ 2 := pow_le_pow_left₀ (by norm_num) u1 2
    nlinarith

/-- The mass bound at the second maximum is above the tail bound. -/
theorem P_gt {M P : ℝ} (hM : M ^ 2 * (4 * Real.pi) = P) (hlo : 0.8306 ≤ M) : 865 / 100 < P := by
  rw [← hM]
  have h2 : 0.8306 ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ (by norm_num) hlo 2
  have pi6 := Real.pi_gt_d6
  nlinarith

