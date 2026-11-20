import Checked.Math.GelfandPDEExists
import Checked.Math.GNegProfile

/-! Gelfand problem in the unit ball of three-dimensional space with a non-positive parameter: a radial
classical solution of Δu + λ eᵘ = 0, u = 0 on the sphere, exists for every λ ≤ 0. Hence the hypothesis
`0 < lam` of `Checked.Math.GelfandPDEExists.gelfand_pde_radial_exists` is redundant
(`Checked.Trust.NecessityBE.gelfand_pde_radial_exists_r1`, listed in TRUST_MAP.md).

For λ < 0, μ = −λ: the profile v'' + (2/s)v' = e^{min v M}, v(0) = 0 (clamped, from
`Checked.Math.GNegProfile`) grows at least like s²/6; the intermediate value theorem gives c with
v(c) = log(μ/c²), the clamp is inactive on [0, c], and u(x) = v(c‖x‖) + log(c²/μ). -/

namespace Checked.Math.GNegExists
open Set Filter Topology InnerProductSpace Laplacian Metric

set_option maxHeartbeats 1000000 in
theorem exists_neg (lam : ℝ) (hneg : lam < 0) :
    ∃ u : EuclideanSpace ℝ (Fin 3) → ℝ,
      ContDiffOn ℝ 2 u (ball 0 1) ∧ ContinuousOn u (closedBall 0 1) ∧
      (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → u x = 0) ∧
      (∃ g : ℝ → ℝ, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, u x = g ‖x‖) ∧
      (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ u x + lam * Real.exp (u x) = 0) := by
  have hμ : 0 < -lam := by linarith
  have hlam : lam ≠ 0 := hneg.ne
  -- the choice of the clamp level
  set clo : ℝ := min (1 / 2) (Real.sqrt (-lam) / 2) with hclo
  have hclo0 : 0 < clo := lt_min (by norm_num) (by have := Real.sqrt_pos.2 hμ; linarith)
  have hclo12 : clo ≤ 1 / 2 := min_le_left _ _
  have hclo2 : clo ^ 2 ≤ -lam / 4 := by
    have h1 : clo ≤ Real.sqrt (-lam) / 2 := min_le_right _ _
    have h2 : (Real.sqrt (-lam) / 2) ^ 2 = -lam / 4 := by
      rw [div_pow, Real.sq_sqrt hμ.le]; norm_num
    rw [← h2]; exact pow_le_pow_left₀ hclo0.le h1 2
  set M : ℝ := Real.log (-lam / clo ^ 2) with hMdef
  have hlog4 : (1 : ℝ) / 8 < Real.log 4 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    have h1 : Real.exp (1 / 8) ≤ Real.exp 1 := Real.exp_le_exp.2 (by norm_num)
    have h2 := Real.exp_one_lt_d9
    linarith
  have hM4 : Real.log 4 ≤ M := by
    rw [hMdef]
    apply Real.log_le_log (by norm_num)
    rw [le_div_iff₀ (by positivity)]; linarith
  have hM8 : 1 / 8 ≤ M := by linarith
  have hM0 : 0 ≤ M := by linarith
  set T : ℝ := 6 * (-lam) + 3 with hTdef
  have hT : 1 / 2 ≤ T := by rw [hTdef]; linarith
  obtain ⟨W, Φ, hw, hφ0, hφ, h0, hw8⟩ :=
    Checked.Math.GNegProfile.gn_exists_solution M T hM8 hT
  obtain ⟨wmono, wlow⟩ := Checked.Math.GNegProfile.gn_profile_lower M T hM0 (by linarith)
    W Φ hw hφ0 hφ h0
  have cW : ContinuousOn W (Icc 0 T) := fun t ht => (hw t ht).continuousWithinAt
  have hcloT : clo ≤ T := by linarith
  set hh : ℝ → ℝ := fun c => W c - Real.log (-lam / c ^ 2) with hhdef
  have hcont : ContinuousOn hh (Icc clo T) := by
    have hpos : ∀ c ∈ Icc clo T, (0 : ℝ) < c := fun c hc => lt_of_lt_of_le hclo0 hc.1
    refine (cW.mono (Icc_subset_Icc hclo0.le le_rfl)).sub ?_
    refine ContinuousOn.log (continuousOn_const.div (continuousOn_id.pow 2) ?_) ?_
    · intro c hc; have := hpos c hc; positivity
    · intro c hc; have := hpos c hc; positivity
  have hlo : hh clo ≤ 0 := by
    simp only [hhdef]
    have := hw8 clo ⟨hclo0.le, hclo12⟩
    rw [← hMdef]; linarith
  have hhi : 0 ≤ hh T := by
    simp only [hhdef]
    have h1 := wlow T ⟨by linarith, le_rfl⟩
    have hT3 : 3 ≤ T := by rw [hTdef]; linarith
    have hT2 : 1 ≤ T ^ 2 := by nlinarith
    have h2 : Real.log (-lam / T ^ 2) ≤ -lam / T ^ 2 - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    have h3 : -lam / T ^ 2 ≤ -lam := div_le_self hμ.le hT2
    have h4 : -lam ≤ T ^ 2 / 6 := by rw [hTdef]; nlinarith
    linarith
  obtain ⟨s, hs, hsv⟩ := intermediate_value_Icc hcloT hcont ⟨hlo, hhi⟩
  simp only [hhdef] at hsv
  have hs0 : 0 < s := lt_of_lt_of_le hclo0 hs.1
  have hsT : s ≤ T := hs.2
  have hWs : W s = Real.log (-lam / s ^ 2) := by linarith
  have hwM : ∀ t ∈ Icc (0 : ℝ) s, W t ≤ M := by
    intro t ht
    have h1 := wmono ⟨ht.1, ht.2.trans hsT⟩ ⟨hs0.le, hsT⟩ ht.2
    rw [hWs] at h1
    refine h1.trans (Real.log_le_log (by positivity) ?_)
    apply div_le_div_of_nonneg_left hμ.le (by positivity)
    exact pow_le_pow_left₀ hclo0.le hs.1 2
  have sub : Icc (0 : ℝ) s ⊆ Icc 0 T := Icc_subset_Icc le_rfl hsT
  have hw' : ∀ t ∈ Icc (0 : ℝ) s, HasDerivWithinAt W (Φ t) (Icc 0 s) t := fun t ht =>
    (hw t (sub ht)).mono sub
  have hφ0' : ContinuousWithinAt Φ (Icc 0 s) 0 := hφ0.mono sub
  have hφ' : ∀ t ∈ Ioc (0 : ℝ) s,
      HasDerivWithinAt Φ (-(2 / t * Φ t) + Real.exp (W t)) (Icc 0 s) t := by
    intro t ht
    have := (hφ t ⟨ht.1, ht.2.trans hsT⟩).mono sub
    rwa [min_eq_left (hwM t (Ioc_subset_Icc_self ht))] at this
  obtain ⟨hφb, hwb, hDb⟩ :=
    Checked.Math.GNegProfile.gn_profile_bounds M s hs0 W Φ hw' hφ0' hφ' h0 hwM
  set Bm : ℝ := Real.exp M with hBm
  have hBm1 : 1 ≤ Bm := Real.one_le_exp hM0
  set K : ℝ := Bm ^ 2 with hK0
  have hBK : Bm ≤ K := by rw [hK0]; nlinarith
  have hK0' : 0 ≤ K := by positivity
  set c : ℝ := Real.log (s ^ 2 / -lam) with hc
  have hec : Real.exp c = s ^ 2 / -lam := Real.exp_log (by positivity)
  set F : ℝ → ℝ := fun ρ => W (s * ρ) + c with hF
  set F1 : ℝ → ℝ := fun ρ => s * Φ (s * ρ) with hF1d
  set F2 : ℝ → ℝ := fun ρ => s ^ 2 * (-(2 / (s * ρ) * Φ (s * ρ)) + Real.exp (W (s * ρ)))
    with hF2d
  obtain ⟨R, hRd⟩ : ∃ R : ℝ, R = 1 := ⟨1, rfl⟩
  have hR0 : 0 < R := by rw [hRd]; norm_num
  have mem : ∀ ρ ∈ Ioo 0 R, s * ρ ∈ Ioo 0 s := fun ρ hρ =>
    ⟨mul_pos hs0 hρ.1, mul_lt_of_lt_one_right hs0 (hRd ▸ hρ.2)⟩
  have memc : ∀ ρ ∈ Icc 0 R, s * ρ ∈ Icc 0 s := fun ρ hρ =>
    ⟨mul_nonneg hs0.le hρ.1, mul_le_of_le_one_right hs0.le (hRd ▸ hρ.2)⟩
  have dW : ∀ t ∈ Ioo 0 s, HasDerivAt W (Φ t) t := fun t ht =>
    (hw' t ⟨ht.1.le, ht.2.le⟩).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  have dΦ : ∀ t ∈ Ioo 0 s, HasDerivAt Φ (-(2 / t * Φ t) + Real.exp (W t)) t := fun t ht =>
    (hφ' t ⟨ht.1, ht.2.le⟩).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  have hF1 : ∀ ρ ∈ Ioo 0 R, HasDerivAt F (F1 ρ) ρ := by
    intro ρ hρ
    have h := ((dW _ (mem ρ hρ)).comp ρ ((hasDerivAt_id ρ).const_mul s)).add_const c
    convert h using 1
    all_goals first | rfl | (simp only [hF1d]; ring)
  have hF2 : ∀ ρ ∈ Ioo 0 R, HasDerivAt F1 (F2 ρ) ρ := by
    intro ρ hρ
    have h := ((dΦ _ (mem ρ hρ)).comp ρ ((hasDerivAt_id ρ).const_mul s)).const_mul s
    convert h using 1
    all_goals first | rfl | (simp only [hF2d]; ring)
  have cΦ : ∀ t ∈ Ioo 0 s, ContinuousAt Φ t := fun t ht => (dΦ t ht).continuousAt
  have hF2c : ContinuousOn F2 (Ioo 0 R) := by
    intro ρ hρ
    have hm := mem ρ hρ
    have ct : ContinuousAt (fun ρ : ℝ => s * ρ) ρ := (continuous_const.mul continuous_id).continuousAt
    have c1 : ContinuousAt (fun ρ => Φ (s * ρ)) ρ := (cΦ _ hm).comp ct
    have c2 : ContinuousAt (fun ρ => W (s * ρ)) ρ := (dW _ hm).continuousAt.comp ct
    exact (continuousAt_const.mul (((continuousAt_const.div ct hm.1.ne').mul c1).neg.add
      c2.rexp)).continuousWithinAt
  -- bounds at the centre
  set L : ℝ := s ^ 2 / 3 with hL
  set C : ℝ := s ^ 4 * K + s ^ 2 * K with hC
  have key : ∀ t ∈ Ioo 0 s, |Φ t / t - 1 / 3| ≤ K * t ^ 2 ∧
      |3 * (Φ t / t) - Real.exp (W t)| ≤ K * t ^ 2 / 15 := by
    intro t ht
    have htc : t ∈ Icc 0 s := ⟨ht.1.le, ht.2.le⟩
    have hA := hDb t htc
    have hwl := (hwb t htc).1
    have hwu := (hwb t htc).2
    have he1 : 1 ≤ Real.exp (W t) := Real.one_le_exp hwl
    have he2 : |Real.exp (W t) - Real.exp 0| ≤ Bm * |W t - 0| :=
      Checked.Math.GExistsRight.exp_sub_le_of_le (hwM t htc) hM0
    rw [Real.exp_zero, sub_zero, abs_of_nonneg (by linarith), abs_of_nonneg hwl] at he2
    have ht0 : 0 < t := ht.1
    have ht3 : 0 < t ^ 3 := by positivity
    have eA : 3 * (Φ t / t) - Real.exp (W t) =
        (3 * (t ^ 2 * Φ t) - t ^ 3 * Real.exp (W t)) / t ^ 3 := by
      field_simp
    have b2 : |3 * (Φ t / t) - Real.exp (W t)| ≤ K * t ^ 2 / 15 := by
      rw [eA, abs_div, abs_of_pos ht3, div_le_iff₀ ht3]
      calc _ ≤ Bm ^ 2 * t ^ 5 / 15 := hA
        _ = K * t ^ 2 / 15 * t ^ 3 := by rw [hK0]; ring
    refine ⟨?_, b2⟩
    have e1 : Φ t / t - 1 / 3 = (3 * (Φ t / t) - Real.exp (W t)) / 3 +
        (Real.exp (W t) - 1) / 3 := by ring
    rw [e1]
    have b3 : |(Real.exp (W t) - 1) / 3| ≤ K * t ^ 2 / 18 := by
      rw [abs_div, abs_of_nonneg (by linarith : (0 : ℝ) ≤ Real.exp (W t) - 1),
        abs_of_pos (by norm_num : (0 : ℝ) < 3), div_le_iff₀ (by norm_num : (0 : ℝ) < 3)]
      have : Bm * W t ≤ Bm * (Bm * t ^ 2 / 6) :=
        mul_le_mul_of_nonneg_left hwu (by linarith)
      have e : K * t ^ 2 / 18 * 3 = Bm * (Bm * t ^ 2 / 6) := by rw [hK0]; ring
      linarith
    have b4 : |(3 * (Φ t / t) - Real.exp (W t)) / 3| ≤ K * t ^ 2 / 45 := by
      rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 3), div_le_iff₀ (by norm_num : (0 : ℝ) < 3)]
      linarith [b2]
    have hKt : 0 ≤ K * t ^ 2 := by positivity
    calc _ ≤ _ := abs_add_le _ _
      _ ≤ K * t ^ 2 / 45 + K * t ^ 2 / 18 := add_le_add b4 b3
      _ ≤ K * t ^ 2 := by linarith
  have hs4 : 0 ≤ s ^ 4 * K := by positivity
  have hs2 : 0 ≤ s ^ 2 * K := by positivity
  have hM : ∀ ρ ∈ Ioo 0 R, |F1 ρ / ρ - L| ≤ C * ρ := by
    intro ρ hρ
    have hm := mem ρ hρ
    have k := (key _ hm).1
    have hρ0 : 0 < ρ := hρ.1
    have hρ1 : ρ < 1 := hRd ▸ hρ.2
    have e : F1 ρ / ρ - L = s ^ 2 * (Φ (s * ρ) / (s * ρ) - 1 / 3) := by
      simp only [hF1d, hL]; field_simp
    rw [e, abs_mul, abs_of_nonneg (by positivity)]
    calc s ^ 2 * |Φ (s * ρ) / (s * ρ) - 1 / 3| ≤ s ^ 2 * (K * (s * ρ) ^ 2) :=
          mul_le_mul_of_nonneg_left k (by positivity)
      _ = s ^ 4 * K * ρ * ρ := by ring
      _ ≤ s ^ 4 * K * ρ := by nlinarith [mul_nonneg hs4 hρ0.le]
      _ ≤ C * ρ := by
          apply mul_le_mul_of_nonneg_right _ hρ0.le
          simp only [hC]; linarith
  have hK : ∀ ρ ∈ Ioo 0 R, |F2 ρ - F1 ρ / ρ| ≤ C * ρ := by
    intro ρ hρ
    have hm := mem ρ hρ
    have k := (key _ hm).2
    have hρ0 : 0 < ρ := hρ.1
    have hρ1 : ρ < 1 := hRd ▸ hρ.2
    have e : F2 ρ - F1 ρ / ρ = -(s ^ 2 * (3 * (Φ (s * ρ) / (s * ρ)) - Real.exp (W (s * ρ)))) := by
      simp only [hF1d, hF2d]; field_simp; ring
    rw [e, abs_neg, abs_mul, abs_of_nonneg (by positivity)]
    calc s ^ 2 * |3 * (Φ (s * ρ) / (s * ρ)) - Real.exp (W (s * ρ))|
          ≤ s ^ 2 * (K * (s * ρ) ^ 2 / 15) :=
          mul_le_mul_of_nonneg_left k (by positivity)
      _ ≤ s ^ 4 * K * ρ * ρ := by
          have : 0 ≤ s ^ 4 * K * ρ * ρ := by positivity
          have e2 : s ^ 2 * (K * (s * ρ) ^ 2 / 15) = s ^ 4 * K * ρ * ρ / 15 := by ring
          rw [e2]; linarith
      _ ≤ s ^ 4 * K * ρ := by nlinarith [mul_nonneg hs4 hρ0.le]
      _ ≤ C * ρ := by
          apply mul_le_mul_of_nonneg_right _ hρ0.le
          simp only [hC]; linarith
  have hquad : ∀ ρ ∈ Ico 0 R, |F ρ - F 0| ≤ C * ρ ^ 2 := by
    intro ρ hρ
    have hm := memc ρ ⟨hρ.1, hρ.2.le⟩
    have b := hwb _ hm
    have e : F ρ - F 0 = W (s * ρ) := by simp [hF, h0]
    rw [e, abs_of_nonneg b.1]
    have h1 : W (s * ρ) ≤ Bm * (s ^ 2 * ρ ^ 2) / 6 := by
      have := b.2; rw [mul_pow] at this; linarith
    have h2 : Bm * (s ^ 2 * ρ ^ 2) ≤ K * (s ^ 2 * ρ ^ 2) :=
      mul_le_mul_of_nonneg_right hBK (by positivity)
    have h3 : 0 ≤ K * (s ^ 2 * ρ ^ 2) := by positivity
    have h4 : 0 ≤ s ^ 4 * K * ρ ^ 2 := by positivity
    have e5 : C * ρ ^ 2 = s ^ 4 * K * ρ ^ 2 + K * (s ^ 2 * ρ ^ 2) := by simp only [hC]; ring
    linarith
  -- the solution
  refine ⟨fun x => F ‖x‖, ?_, ?_, ?_, ⟨F, fun x _ => rfl⟩, ?_⟩
  · intro x hx
    rw [mem_ball_zero_iff] at hx
    refine ContDiffAt.contDiffWithinAt ?_
    by_cases hx0 : x = 0
    · subst hx0
      exact Checked.Math.RadialC2.contDiffAt_zero_radial hR0 hF1 hF2 hF2c hM hK hquad
    · have hr : ‖x‖ ∈ Ioo 0 R := ⟨norm_pos_iff.2 hx0, by rw [hRd]; exact hx⟩
      have hFc : ContDiffOn ℝ 2 F (Ioo 0 R) :=
        Checked.Math.GelfandPDEExists.contDiffOn_two_of_derivs isOpen_Ioo hF1 hF2 hF2c
      exact (hFc.contDiffAt (isOpen_Ioo.mem_nhds hr)).comp x (contDiffAt_norm ℝ hx0)
  · have cW' : ContinuousOn W (Icc 0 s) := fun t ht => (hw' t ht).continuousWithinAt
    have cF : ContinuousOn F (Icc 0 1) := by
      have : ContinuousOn (fun ρ => W (s * ρ)) (Icc 0 1) :=
        cW'.comp (continuous_const.mul continuous_id).continuousOn
          (fun ρ hρ => memc ρ (hRd ▸ hρ))
      exact this.add continuousOn_const
    exact cF.comp continuous_norm.continuousOn (fun x hx =>
      ⟨norm_nonneg x, mem_closedBall_zero_iff.1 hx⟩)
  · intro x hx
    simp only [hF, hx, mul_one]
    rw [← Real.exp_eq_one_iff, Real.exp_add, hec, hWs, Real.exp_log (by positivity)]
    field_simp
  · intro x hx
    rw [mem_ball_zero_iff] at hx
    by_cases hx0 : x = 0
    · subst hx0
      rw [Checked.Math.RadialC2.laplacian_radial_zero hR0 hF1 hF2 hM hquad,
        finrank_euclideanSpace_fin]
      simp only [norm_zero, hF, mul_zero, h0, zero_add, hec, hL]
      field_simp
      ring
    · have hr : ‖x‖ ∈ Ioo 0 R := ⟨norm_pos_iff.2 hx0, by rw [hRd]; exact hx⟩
      have hL' := Checked.Math.RadialLaplacian.laplacian_radial (f := F) (f' := F1)
        (f'' := F2 ‖x‖) hx0
        (by filter_upwards [isOpen_Ioo.mem_nhds hr] with ρ hρ using hF1 ρ hρ)
        (hF2 _ hr)
      rw [hL', finrank_euclideanSpace_fin]
      have hr0 : 0 < ‖x‖ := hr.1
      simp only [hF, hF1d, hF2d, Real.exp_add, hec]
      field_simp
      ring

/-- Radial classical solutions of the Gelfand problem in the unit ball of ℝ³ for every λ ≤ 0. -/
theorem exists_nonpos (lam : ℝ) (hle : lam ≤ 0) :
    ∃ u : EuclideanSpace ℝ (Fin 3) → ℝ,
      ContDiffOn ℝ 2 u (ball 0 1) ∧ ContinuousOn u (closedBall 0 1) ∧
      (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → u x = 0) ∧
      (∃ g : ℝ → ℝ, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, u x = g ‖x‖) ∧
      (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ u x + lam * Real.exp (u x) = 0) := by
  rcases eq_or_lt_of_le hle with h | h
  · subst h
    refine ⟨fun _ => 0, contDiffOn_const, continuousOn_const, fun _ _ => rfl,
      ⟨fun _ => 0, fun _ _ => rfl⟩, fun x _ => ?_⟩
    simp
  · exact exists_neg lam h

end Checked.Math.GNegExists
