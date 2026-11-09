/-- Antiderivative of `η − 1 + e^{−η}`. -/
theorem linF_deriv (η : ℝ) :
    HasDerivAt (fun η : ℝ => η ^ 2 / 2 - η + 1 - Real.exp (-η)) (η - 1 + Real.exp (-η)) η := by
  have hE : HasDerivAt (fun η : ℝ => Real.exp (-η)) (-Real.exp (-η)) η := by
    simpa using (hasDerivAt_neg η).exp
  exact (((((hasDerivAt_pow 2 η).div_const 2).sub (hasDerivAt_id' η)).add_const 1).sub hE).congr_deriv
    (by ring)

/-- The solution of the linear equation `q' = −K f q − β (1 − p²)` along `f = η − 1 + e^{−η}`,
`p = 1 − e^{−η}` with value `q₀` at zero, by an integrating factor. -/
theorem linQ_deriv (K β q₀ η : ℝ) :
    HasDerivAt (fun η => Real.exp (-(K * (η ^ 2 / 2 - η + 1 - Real.exp (-η)))) *
      (q₀ - β * ∫ s in (0 : ℝ)..η,
        Real.exp (K * (s ^ 2 / 2 - s + 1 - Real.exp (-s))) * (1 - (1 - Real.exp (-s)) ^ 2)))
      (-(K * (η - 1 + Real.exp (-η)) * (Real.exp (-(K * (η ^ 2 / 2 - η + 1 - Real.exp (-η)))) *
        (q₀ - β * ∫ s in (0 : ℝ)..η,
          Real.exp (K * (s ^ 2 / 2 - s + 1 - Real.exp (-s))) * (1 - (1 - Real.exp (-s)) ^ 2))))
        - β * (1 - (1 - Real.exp (-η)) ^ 2)) η := by
  have hφ : Continuous (fun s : ℝ =>
      Real.exp (K * (s ^ 2 / 2 - s + 1 - Real.exp (-s))) * (1 - (1 - Real.exp (-s)) ^ 2)) := by
    fun_prop
  have hI := (hφ.integral_hasStrictDerivAt 0 η).hasDerivAt
  have hX := ((linF_deriv η).const_mul K).neg.exp
  have := hX.mul ((hasDerivAt_const η q₀).sub (hI.const_mul β))
  refine this.congr_deriv ?_
  have h1 : Real.exp (-(K * (η ^ 2 / 2 - η + 1 - Real.exp (-η)))) *
      Real.exp (K * (η ^ 2 / 2 - η + 1 - Real.exp (-η))) = 1 := by
    rw [← Real.exp_add]; simp
  simp only [Pi.sub_apply]
  linear_combination (-β * (1 - (1 - Real.exp (-η)) ^ 2)) * h1

/-- The profile `f = η − 1 + e^{−η}`, `p = 1 − e^{−η}`. -/
theorem linProfile :
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt (fun η : ℝ => η - 1 + Real.exp (-η))
      ((fun η : ℝ => 1 - Real.exp (-η)) η) (Ici 0) η) ∧
    Tendsto (fun η : ℝ => 1 - Real.exp (-η)) atTop (𝓝 1) ∧
    (∀ η ∈ Ici (0 : ℝ), -1 ≤ (fun η : ℝ => 1 - Real.exp (-η)) η ∧
      (fun η : ℝ => 1 - Real.exp (-η)) η ≤ 1) := by
  refine ⟨fun η _ => ?_, ?_, fun η hη => ?_⟩
  · have hE : HasDerivAt (fun η : ℝ => Real.exp (-η)) (-Real.exp (-η)) η := by
      simpa using (hasDerivAt_neg η).exp
    exact (((hasDerivAt_id' η).sub_const 1).add hE).congr_deriv (by ring) |>.hasDerivWithinAt
  · have h0 : Tendsto (fun η : ℝ => Real.exp (-η)) atTop (𝓝 0) := Real.tendsto_exp_neg_atTop_nhds_zero
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub h0
  · have h1 : Real.exp (-η) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [mem_Ici.mp hη])
    have h2 := Real.exp_pos (-η)
    constructor <;> simp only <;> linarith
