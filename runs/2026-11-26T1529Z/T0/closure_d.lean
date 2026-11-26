import Readings.T0

open Complex Filter Topology Finset Asymptotics
namespace ExternalT0
open T0

/-- The terms of the Clausen-type sine series. -/
noncomputable def clTerm (θ : ℝ) (k : ℕ) : ℝ := Real.sin ((k + 1) * θ) / ((k : ℝ) + 1) ^ 2

/-- The Clausen-type sine series `Σ_{k≥1} sin(kθ)/k²`. -/
noncomputable def cl (θ : ℝ) : ℝ := ∑' k : ℕ, clTerm θ k

lemma summable_inv_sq : Summable (fun k : ℕ => (((k : ℝ) + 1) ^ 2)⁻¹) := by
  have := (summable_nat_add_iff 1).mpr (Real.summable_nat_pow_inv.mpr one_lt_two)
  simpa using this

lemma summable_cl (θ : ℝ) : Summable (clTerm θ) := by
  refine Summable.of_norm_bounded summable_inv_sq (fun k => ?_)
  rw [clTerm, Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : (0:ℝ) < ((k:ℝ) + 1) ^ 2), div_eq_mul_inv]
  have := Real.abs_sin_le_one ((k + 1) * θ)
  have h0 : (0:ℝ) ≤ (((k:ℝ) + 1) ^ 2)⁻¹ := by positivity
  nlinarith

/-- Tail bound: `Σ_{k ≥ K} 1/(k+1)² ≤ 2/(K+1)`. -/
lemma tail_le (K : ℕ) : ∑' k : ℕ, ((((k + K : ℕ) : ℝ) + 1) ^ 2)⁻¹ ≤ 2 / ((K : ℝ) + 1) := by
  apply Real.tsum_le_of_sum_range_le (fun k => by positivity)
  intro n
  calc ∑ k ∈ Finset.range n, ((((k + K : ℕ) : ℝ) + 1) ^ 2)⁻¹
      = ∑ k ∈ Finset.range n, (((K + 1 + k : ℕ) : ℝ) ^ 2)⁻¹ := by
        apply Finset.sum_congr rfl; intro k _; push_cast; ring_nf; done
    _ = ∑ i ∈ Finset.Ico (K + 1) (n + K + 1), ((i : ℝ) ^ 2)⁻¹ := by
        rw [Finset.sum_Ico_eq_sum_range, show n + K + 1 - (K + 1) = n by omega]
    _ = ∑ i ∈ Finset.Ioo K (n + K + 1), ((i : ℝ) ^ 2)⁻¹ := by
        congr 1
    _ ≤ 2 / ((K : ℝ) + 1) := sum_Ioo_inv_sq_le K (n + K + 1)

/-- Main estimate: `|cl θ − θ log(1/θ)| ≤ 4θ` for `0 < θ ≤ 1/2`. -/
theorem cl_approx (θ : ℝ) (hθ : 0 < θ) (hθ2 : θ ≤ 1 / 2) :
    |cl θ - θ * Real.log (1 / θ)| ≤ 4 * θ := by
  set K := ⌊1 / θ⌋₊ with hK
  have hKle : (K : ℝ) ≤ 1 / θ := Nat.floor_le (by positivity)
  have hKlt : 1 / θ < (K : ℝ) + 1 := Nat.lt_floor_add_one _
  have hK1 : 1 ≤ K := by
    apply Nat.le_floor; rw [le_div_iff₀ hθ]; push_cast; linarith
  have hK1r : (1 : ℝ) ≤ K := by exact_mod_cast hK1
  have hKθ : (K : ℝ) * θ ≤ 1 := by rw [le_div_iff₀ hθ] at hKle; linarith
  set f := clTerm θ with hf
  have hsplit := (summable_cl θ).sum_add_tsum_nat_add K
  -- head
  have hhead : |∑ k ∈ Finset.range K, f k - θ * ∑ k ∈ Finset.range K, 1 / ((k : ℝ) + 1)| ≤ θ / 4 := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    calc |∑ k ∈ Finset.range K, (f k - θ * (1 / ((k : ℝ) + 1)))|
        ≤ ∑ k ∈ Finset.range K, |f k - θ * (1 / ((k : ℝ) + 1))| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Finset.range K, ((k : ℝ) + 1) * θ ^ 3 / 6 := by
          apply Finset.sum_le_sum; intro k _
          have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
          have hx : 0 < ((k : ℝ) + 1) * θ := by positivity
          have hs1 := Real.sin_le hx.le
          have hs2 := Real.sin_gt_sub_cube hx
          have e : f k - θ * (1 / ((k : ℝ) + 1))
              = (Real.sin ((k + 1) * θ) - (k + 1) * θ) / ((k : ℝ) + 1) ^ 2 := by
            simp only [hf, clTerm]; field_simp
          rw [e, abs_div, abs_of_pos (by positivity : (0:ℝ) < ((k:ℝ) + 1) ^ 2),
            abs_of_nonpos (by linarith), div_le_iff₀ (by positivity)]
          have : (((k:ℝ) + 1) * θ) ^ 3 / 6 = ((k : ℝ) + 1) * θ ^ 3 / 6 * ((k : ℝ) + 1) ^ 2 := by ring
          linarith
      _ = θ ^ 3 / 6 * ∑ k ∈ Finset.range K, ((k : ℝ) + 1) := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; ring
      _ ≤ θ ^ 3 / 6 * ((K : ℝ) * K) := by
          gcongr
          calc ∑ k ∈ Finset.range K, ((k : ℝ) + 1) ≤ ∑ _k ∈ Finset.range K, (K : ℝ) := by
                apply Finset.sum_le_sum; intro k hk
                have := Finset.mem_range.mp hk
                have : (k : ℝ) + 1 ≤ K := by exact_mod_cast this
                exact this
            _ = (K : ℝ) * K := by simp
      _ ≤ θ / 4 := by
          have h2 : ((K:ℝ) * θ) ^ 2 ≤ 1 := by
            have : 0 ≤ (K:ℝ) * θ := by positivity
            nlinarith
          have : θ ^ 3 / 6 * ((K:ℝ) * K) = θ * ((K:ℝ) * θ) ^ 2 / 6 := by ring
          rw [this]; nlinarith
  -- tail
  have htail : |∑' k : ℕ, f (k + K)| ≤ 2 * θ := by
    calc |∑' k : ℕ, f (k + K)| ≤ ∑' k : ℕ, |f (k + K)| :=
          (Real.norm_eq_abs _ ▸ norm_tsum_le_tsum_norm ((summable_nat_add_iff K).mpr (summable_cl θ)).norm)
      _ ≤ ∑' k : ℕ, ((((k + K : ℕ) : ℝ) + 1) ^ 2)⁻¹ := by
          apply Summable.tsum_le_tsum _ ((summable_nat_add_iff K).mpr (summable_cl θ)).abs
            ((summable_nat_add_iff K).mpr summable_inv_sq |>.congr (fun k => by push_cast; ring_nf))
          intro k
          simp only [hf, clTerm]
          rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < (((k + K : ℕ) : ℝ) + 1) ^ 2), div_eq_mul_inv]
          push_cast
          have := Real.abs_sin_le_one (((k:ℝ) + K + 1) * θ)
          have h0 : (0:ℝ) ≤ ((((k:ℝ) + K) + 1) ^ 2)⁻¹ := by positivity
          nlinarith
      _ ≤ 2 / ((K : ℝ) + 1) := tail_le K
      _ ≤ 2 * θ := by
          rw [div_le_iff₀ (by positivity)]
          have : 1 < ((K : ℝ) + 1) * θ := by rw [div_lt_iff₀ hθ] at hKlt; linarith
          nlinarith
  -- harmonic
  have hH : ∑ k ∈ Finset.range K, 1 / ((k : ℝ) + 1) = (harmonic K : ℝ) := by
    simp [harmonic]
  have hlog1 : Real.log K ≤ Real.log (1 / θ) := Real.log_le_log (by positivity) hKle
  have hlog2 : Real.log (1 / θ) ≤ Real.log ↑(K + 1) := by
    apply Real.log_le_log (by positivity); push_cast; linarith
  have hb1 := log_add_one_le_harmonic K
  have hb2 := harmonic_le_one_add_log K
  have hharm : |θ * ∑ k ∈ Finset.range K, 1 / ((k : ℝ) + 1) - θ * Real.log (1 / θ)| ≤ θ := by
    rw [hH, ← mul_sub, abs_mul, abs_of_pos hθ]
    have : |(harmonic K : ℝ) - Real.log (1 / θ)| ≤ 1 := by rw [abs_le]; constructor <;> linarith
    nlinarith
  have hcl : cl θ = ∑ k ∈ Finset.range K, f k + ∑' k : ℕ, f (k + K) := by
    unfold cl; exact hsplit.symm
  rw [hcl]
  calc |∑ k ∈ Finset.range K, f k + ∑' k : ℕ, f (k + K) - θ * Real.log (1 / θ)|
      = |(∑ k ∈ Finset.range K, f k - θ * ∑ k ∈ Finset.range K, 1 / ((k : ℝ) + 1))
          + ∑' k : ℕ, f (k + K)
          + (θ * ∑ k ∈ Finset.range K, 1 / ((k : ℝ) + 1) - θ * Real.log (1 / θ))| := by
        congr 1; ring
    _ ≤ |∑ k ∈ Finset.range K, f k - θ * ∑ k ∈ Finset.range K, 1 / ((k : ℝ) + 1)|
          + |∑' k : ℕ, f (k + K)|
          + |θ * ∑ k ∈ Finset.range K, 1 / ((k : ℝ) + 1) - θ * Real.log (1 / θ)| := abs_add_three _ _ _
    _ ≤ θ / 4 + 2 * θ + θ := by linarith
    _ ≤ 4 * θ := by linarith


lemma im_R (s : ℝ) (hs : 0 < s) :
    (Li2 (Complex.exp (-(2 * Complex.I / s))) / (2 * (s : ℂ) ^ 2)).im = -cl (2 / s) / (2 * s ^ 2) := by
  set z := Complex.exp (-(2 * Complex.I / s)) with hz
  have hzk : ∀ k : ℕ, z ^ (k + 1) = Complex.exp (((-((k + 1) * (2 / s)) : ℝ) : ℂ) * Complex.I) := by
    intro k; rw [hz, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
  have hden : ∀ k : ℕ, ((k : ℂ) + 1) ^ 2 = (((k : ℝ) + 1) ^ 2 : ℝ) := by intro k; push_cast; ring
  have hsum : Summable (fun k : ℕ => z ^ (k + 1) / ((k : ℂ) + 1) ^ 2) := by
    refine Summable.of_norm_bounded summable_inv_sq (fun k => ?_)
    rw [hzk, hden, norm_div, Complex.norm_exp_ofReal_mul_I, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity), one_div]
  have h2 : (2 * (s : ℂ) ^ 2) = ((2 * s ^ 2 : ℝ) : ℂ) := by push_cast; ring
  rw [h2, Complex.div_ofReal_im]
  congr 1
  unfold Li2 cl
  rw [Complex.im_tsum hsum, ← tsum_neg]
  congr 1; funext k
  rw [hzk, hden, Complex.div_ofReal_im, Complex.exp_ofReal_mul_I_im, clTerm, Real.sin_neg]
  push_cast; ring_nf

theorem finite_term' : type_of% @T0.finite_term := by
  intro R
  have key : ∀ s : ℝ, 4 ≤ s → |(R s).im + Real.log s / s ^ 3| ≤ 5 * (1 / s ^ 3) := by
    intro s hs4
    have hs : 0 < s := by linarith
    have hR : (R s).im = -cl (2 / s) / (2 * s ^ 2) := im_R s hs
    have hθ : 0 < 2 / s := by positivity
    have hθ2 : 2 / s ≤ 1 / 2 := by rw [div_le_div_iff₀ hs (by norm_num)]; linarith
    have happ := cl_approx (2 / s) hθ hθ2
    have hlog : Real.log (1 / (2 / s)) = Real.log s - Real.log 2 := by
      rw [one_div_div, Real.log_div hs.ne' (by norm_num)]
    rw [hlog] at happ
    set E := cl (2 / s) - 2 / s * (Real.log s - Real.log 2) with hE
    have hcl : cl (2 / s) = 2 / s * (Real.log s - Real.log 2) + E := by rw [hE]; ring
    rw [hR, hcl]
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hl2' : Real.log 2 < 1 := by
      have := Real.log_two_lt_d9; linarith
    have e : -(2 / s * (Real.log s - Real.log 2) + E) / (2 * s ^ 2) + Real.log s / s ^ 3
        = Real.log 2 / s ^ 3 - E / (2 * s ^ 2) := by field_simp; ring
    rw [e]
    have hEb : |E / (2 * s ^ 2)| ≤ 4 / s ^ 3 := by
      rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < 2 * s ^ 2), div_le_div_iff₀ (by positivity) (by positivity)]
      have : 4 * (2 / s) * (s ^ 3) = 8 * s ^ 2 := by field_simp; norm_num
      nlinarith [abs_nonneg E]
    have h1 : |Real.log 2 / s ^ 3| ≤ 1 / s ^ 3 := by
      rw [abs_div, abs_of_pos hl2, abs_of_pos (by positivity)]; gcongr
    calc |Real.log 2 / s ^ 3 - E / (2 * s ^ 2)| ≤ |Real.log 2 / s ^ 3| + |E / (2 * s ^ 2)| := abs_sub _ _
      _ ≤ 1 / s ^ 3 + 4 / s ^ 3 := by linarith
      _ = 5 * (1 / s ^ 3) := by ring
  have hO : (fun s : ℝ => (R s).im + Real.log s / s ^ 3) =O[atTop] (fun s : ℝ => 1 / s ^ 3) := by
    apply IsBigO.of_bound 5
    filter_upwards [eventually_ge_atTop 4] with s hs
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (by positivity : (0:ℝ) < 1 / s ^ 3)]
    exact key s hs
  refine ⟨hO, ?_⟩
  -- ratio: (R s).im / (-(log s)/s³) = 1 - D s / (log s / s³), with D = O(1/s³)
  have hD : Tendsto (fun s : ℝ => ((R s).im + Real.log s / s ^ 3) / (Real.log s / s ^ 3)) atTop (𝓝 0) := by
    have h1 : (fun s : ℝ => ((R s).im + Real.log s / s ^ 3) / (Real.log s / s ^ 3))
        =O[atTop] (fun s : ℝ => 1 / Real.log s) := by
      apply IsBigO.of_bound 5
      filter_upwards [eventually_ge_atTop 4] with s hs
      have hs0 : 0 < s := by linarith
      have hl : 0 < Real.log s := Real.log_pos (by linarith)
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : 0 < Real.log s / s ^ 3),
        abs_of_pos (by positivity : 0 < 1 / Real.log s), div_le_iff₀ (by positivity)]
      have := key s hs
      have : 5 * (1 / Real.log s) * (Real.log s / s ^ 3) = 5 * (1 / s ^ 3) := by field_simp
      linarith
    apply h1.trans_tendsto
    have := Real.tendsto_log_atTop.inv_tendsto_atTop
    simp only [one_div]; exact this
  have : Tendsto (fun s : ℝ => 1 - ((R s).im + Real.log s / s ^ 3) / (Real.log s / s ^ 3)) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1:ℝ))).sub hD
  apply this.congr'
  filter_upwards [eventually_ge_atTop 4] with s hs
  have hs0 : 0 < s := by linarith
  have hl : 0 < Real.log s := Real.log_pos (by linarith)
  field_simp
  ring

end ExternalT0
#print axioms ExternalT0.cl_approx
#print axioms ExternalT0.finite_term'
