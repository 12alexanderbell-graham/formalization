namespace GTR
open Set Filter Topology

/-- The squeeze: per-segment bounds with errors tending to zero give the limit of the log-advance. -/
theorem lim_D {ε L D : ℕ → ℝ} {K : ℕ} (hε : Tendsto ε atTop (𝓝 0))
    (h1 : ∀ k, K ≤ k → (Real.sqrt 7 / 2 - 16 * ε k) * L k ≤ Real.pi)
    (h2 : ∀ k, K ≤ k → Real.pi ≤ (Real.sqrt 7 / 2 + 16 * ε k) * L k)
    (h3 : ∀ k, K ≤ k → -(1 + 36 * ε k) * L k ≤ D k)
    (h4 : ∀ k, K ≤ k → D k ≤ -(1 - 36 * ε k) * L k) :
    Tendsto D atTop (𝓝 (-(Real.pi / (Real.sqrt 7 / 2)))) := by
  set c := Real.sqrt 7 / 2 with hc
  have cpos : 0 < c := by positivity
  -- eventually the error is small
  have hsmall : ∀ᶠ k in atTop, K ≤ k ∧ 16 * ε k < c / 2 ∧ 36 * ε k < 1 / 2 ∧ -(c / 32) < ε k := by
    have e1 : ∀ᶠ k in atTop, 16 * ε k < c / 2 := by
      have : Tendsto (fun k => 16 * ε k) atTop (𝓝 (16 * 0)) := hε.const_mul 16
      rw [mul_zero] at this
      exact this.eventually (gt_mem_nhds (by linarith))
    have e2 : ∀ᶠ k in atTop, 36 * ε k < 1 / 2 := by
      have : Tendsto (fun k => 36 * ε k) atTop (𝓝 (36 * 0)) := hε.const_mul 36
      rw [mul_zero] at this
      exact this.eventually (gt_mem_nhds (by norm_num))
    have e3 : ∀ᶠ k in atTop, -(c / 32) < ε k := hε.eventually (lt_mem_nhds (by linarith))
    filter_upwards [eventually_ge_atTop K, e1, e2, e3] with k a b c' d using ⟨a, b, c', d⟩
  -- L between pi/(c + 16ε) and pi/(c - 16ε)
  have hLlo : Tendsto (fun k => Real.pi / (c + 16 * ε k)) atTop (𝓝 (Real.pi / c)) := by
    have : Tendsto (fun k => c + 16 * ε k) atTop (𝓝 (c + 16 * 0)) := (hε.const_mul 16).const_add c
    rw [mul_zero, add_zero] at this
    exact tendsto_const_nhds.div this cpos.ne'
  have hLhi : Tendsto (fun k => Real.pi / (c - 16 * ε k)) atTop (𝓝 (Real.pi / c)) := by
    have : Tendsto (fun k => c - 16 * ε k) atTop (𝓝 (c - 16 * 0)) := (hε.const_mul 16).const_sub c
    rw [mul_zero, sub_zero] at this
    exact tendsto_const_nhds.div this cpos.ne'
  have hL : Tendsto L atTop (𝓝 (Real.pi / c)) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hLlo hLhi ?_ ?_
    · filter_upwards [hsmall] with k hk'
      obtain ⟨hk, a, -, a3⟩ := hk'
      have hp : 0 < c + 16 * ε k := by linarith
      rw [div_le_iff₀ hp]; linarith [h2 k hk]
    · filter_upwards [hsmall] with k hk'
      obtain ⟨hk, a, -, a3⟩ := hk'
      have hp : 0 < c - 16 * ε k := by linarith
      rw [le_div_iff₀ hp]; linarith [h1 k hk]
  have hlo : Tendsto (fun k => -(1 + 36 * ε k) * L k) atTop (𝓝 (-(1 + 36 * 0) * (Real.pi / c))) :=
    (((hε.const_mul 36).const_add 1).neg).mul hL
  have hhi : Tendsto (fun k => -(1 - 36 * ε k) * L k) atTop (𝓝 (-(1 - 36 * 0) * (Real.pi / c))) :=
    (((hε.const_mul 36).const_sub 1).neg).mul hL
  norm_num at hlo hhi
  have e : -(Real.pi / c) = -(Real.pi / c) := rfl
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (g := fun k => -(1 + 36 * ε k) * L k)
    (h := fun k => -(1 - 36 * ε k) * L k) ?_ ?_ ?_ ?_
  · simpa using hlo
  · simpa using hhi
  · filter_upwards [hsmall] with k hk' using h3 k hk'.1
  · filter_upwards [hsmall] with k hk' using h4 k hk'.1

theorem lim_q {D q : ℕ → ℝ} {K : ℕ}
    (hD : Tendsto D atTop (𝓝 (-(Real.pi / (Real.sqrt 7 / 2)))))
    (hq : ∀ k, K ≤ k → q k = -Real.exp (D k / 2)) :
    Tendsto q atTop (𝓝 (-Real.exp (-(Real.pi / Real.sqrt 7)))) := by
  have h : Tendsto (fun k => -Real.exp (D k / 2)) atTop
      (𝓝 (-Real.exp (-(Real.pi / (Real.sqrt 7 / 2)) / 2))) :=
    ((Real.continuous_exp.tendsto _).comp (hD.div_const 2)).neg
  have e : -(Real.pi / (Real.sqrt 7 / 2)) / 2 = -(Real.pi / Real.sqrt 7) := by
    have : Real.sqrt 7 ≠ 0 := by positivity
    field_simp
  rw [e] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop K] with k hk using (hq k hk).symm

end GTR
