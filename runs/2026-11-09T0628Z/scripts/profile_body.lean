/-- Exponential profile: f = η − (1 − e^{−aη})/a, f' = p = 1 − e^{−aη}, p' = q = a e^{−aη}. -/
theorem expProfile (a : ℝ) (ha : 0 < a) :
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt (fun η => η - (1 - Real.exp (-a * η)) / a)
        ((fun η => 1 - Real.exp (-a * η)) η) (Ici 0) η) ∧
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt (fun η => 1 - Real.exp (-a * η))
        ((fun η => a * Real.exp (-a * η)) η) (Ici 0) η) ∧
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt (fun η => a * Real.exp (-a * η))
        (-(a * (a * Real.exp (-a * η)))) (Ici 0) η) ∧
    Tendsto (fun η => 1 - Real.exp (-a * η)) atTop (𝓝 1) ∧
    (∀ η ∈ Ici (0 : ℝ), -1 ≤ (fun η => 1 - Real.exp (-a * η)) η ∧
      (fun η => 1 - Real.exp (-a * η)) η ≤ 1) := by
  have hE : ∀ η : ℝ, HasDerivAt (fun η => Real.exp (-a * η)) (-a * Real.exp (-a * η)) η := by
    intro η
    exact ((hasDerivAt_id' η).const_mul (-a)).exp.congr_deriv (by ring)
  refine ⟨fun η _ => ?_, fun η _ => ?_, fun η _ => ?_, ?_, fun η hη => ?_⟩
  · have := ((hasDerivAt_id η).sub (((hasDerivAt_const η (1 : ℝ)).sub (hE η)).div_const a))
    refine (this.congr_deriv ?_).hasDerivWithinAt
    field_simp; ring
  · exact (((hasDerivAt_const η (1 : ℝ)).sub (hE η)).congr_deriv (by ring)).hasDerivWithinAt
  · exact (((hE η).const_mul a).congr_deriv (by ring)).hasDerivWithinAt
  · have h0 : Tendsto (fun η : ℝ => Real.exp (-a * η)) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (neg_lt_zero.mpr ha))
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub h0
  · have h1 : Real.exp (-a * η) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [mem_Ici.mp hη])
    have h2 := Real.exp_pos (-a * η)
    constructor <;> simp only <;> linarith

