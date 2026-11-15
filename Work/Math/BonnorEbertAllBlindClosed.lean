import Mathlib
import Work.Math.BonnorEbertAll
import Work.Math.BonnorEbertAllBlind

/-! Bonnor–Ebert sphere: the blind restatement `Work.Math.BonnorEbertAllBlind.blind_bonnor_ebert_all_extrema`
(ψ continuous on [0, ∞), ψ(0) = 0, right derivative 0 at 0, ψ differentiable at every ξ > 0, the equation in
divergence form `HasDerivAt (x ↦ x² ψ'(x)) (ξ² e^{−ψ ξ}) ξ` for ξ > 0 with ψ' the two-sided `deriv`, mass
(4π)^{−1/2} e^{−ψ/2} ξ² ψ', strict extrema over every radius from the previous extremum on) closed from the
frozen headline `Work.Math.BonnorEbertAll.bonnor_ebert_all_extrema` with w = −ψ and φ = −ψ' on (0, ∞), φ(0) = 0.
The blind hypotheses do not include continuity of ψ' at 0; it is derived: F(x) = x² ψ'(x) is increasing on
(0, ∞) with F' ≤ C x² on (0, 1] (C bounds e^{−ψ} there), and F has limit 0 at 0⁺ because a limit c ≠ 0
would make ψ' ≈ c/x² and ψ unbounded near 0 (`blowup`), contradicting continuity of ψ at 0; so
0 ≤ F(x) ≤ C x³/3 and |ψ'(x)| ≤ C x/3. Written by run 2026-11-15T0028Z. -/

namespace Work.Math.BonnorEbertAllBlindClosed
open Set Filter Topology Work.Math.BonnorEbertAllBlind

/-- A function continuous at 0 from the right cannot have derivative ≥ δ/t² on (0, s0]. -/
theorem blowup {f f' : ℝ → ℝ} {s0 δ : ℝ} (hs0 : 0 < s0) (hδ : 0 < δ)
    (hc : ContinuousWithinAt f (Ici 0) 0) (hd : ∀ t ∈ Ioc 0 s0, HasDerivAt f (f' t) t)
    (hb : ∀ t ∈ Ioc 0 s0, δ / t ^ 2 ≤ f' t) : False := by
  have hG : MonotoneOn (fun t => f t + δ * t⁻¹) (Ioc 0 s0) := by
    have hGd : ∀ t ∈ Ioc (0 : ℝ) s0, HasDerivAt (fun t => f t + δ * t⁻¹) (f' t + δ * (-(t ^ 2)⁻¹)) t :=
      fun t ht => (hd t ht).add ((hasDerivAt_inv ht.1.ne').const_mul δ)
    apply monotoneOn_of_deriv_nonneg (convex_Ioc 0 s0)
    · exact fun t ht => (hGd t ht).continuousAt.continuousWithinAt
    · rw [interior_Ioc]
      exact fun t ht => (hGd t (Ioo_subset_Ioc_self ht)).differentiableAt.differentiableWithinAt
    · rw [interior_Ioc]
      intro t ht
      rw [(hGd t (Ioo_subset_Ioc_self ht)).deriv]
      have := hb t (Ioo_subset_Ioc_self ht)
      have e : δ * (-(t ^ 2)⁻¹) = -(δ / t ^ 2) := by ring
      rw [e]; linarith
  -- f near 0 is within 1 of f 0
  have h1 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), |f ε - f 0| < 1 := by
    have := hc.mono (Ioi_subset_Ici_self)
    have h := (Metric.tendsto_nhds.1 this) 1 one_pos
    filter_upwards [h] with ε hε
    rwa [Real.dist_eq] at hε
  set K := f s0 + δ * s0⁻¹ - f 0 + 1 with hK
  have h2 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < s0 ∧ K < δ * ε⁻¹ := by
    have ht : Tendsto (fun ε : ℝ => δ * ε⁻¹) (𝓝[>] 0) atTop :=
      tendsto_inv_nhdsGT_zero.const_mul_atTop hδ
    filter_upwards [ht.eventually_gt_atTop K, Ioo_mem_nhdsGT hs0] with ε hε hε2
    exact ⟨hε2.2, hε⟩
  obtain ⟨ε, ⟨hf, hlt, hK'⟩, hpos⟩ := ((h1.and h2).and self_mem_nhdsWithin).exists
  have hm := hG ⟨hpos, hlt.le⟩ ⟨hs0, le_rfl⟩ hlt.le
  simp only at hm
  have := abs_lt.1 hf
  linarith [this.1]

theorem F_bounds (ψ : ℝ → ℝ) (hψ : IsRegularSolution ψ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t ∈ Ioc (0 : ℝ) 1, |deriv ψ t| ≤ C * t / 3 := by
  obtain ⟨hcont, h0, hd0, hdiff, hode⟩ := hψ
  -- a lower bound of ψ on [0, 1]
  obtain ⟨m, hm⟩ : ∃ m, ∀ x ∈ Icc (0 : ℝ) 1, m ≤ ψ x := by
    obtain ⟨m, hm⟩ := (isCompact_Icc.bddBelow_image (hcont.mono Icc_subset_Ici_self))
    exact ⟨m, fun x hx => hm ⟨x, hx, rfl⟩⟩
  set C := Real.exp (-m) with hC
  have hCpos : 0 < C := Real.exp_pos _
  set F : ℝ → ℝ := fun x => x ^ 2 * deriv ψ x with hF
  have hFd : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt F (t ^ 2 * Real.exp (-ψ t)) t := fun t ht => hode t ht
  have hψd : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt ψ (F t / t ^ 2) t := by
    intro t ht
    have : F t / t ^ 2 = deriv ψ t := by
      have htne : t ≠ 0 := ne_of_gt (show (0 : ℝ) < t from ht)
      simp only [hF]; field_simp
    rw [this]; exact (hdiff t ht).hasDerivAt
  have hFmono : MonotoneOn F (Ioi 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ioi 0)
    · exact fun t ht => (hFd t ht).continuousAt.continuousWithinAt
    · rw [interior_Ioi]; exact fun t ht => (hFd t ht).differentiableAt.differentiableWithinAt
    · rw [interior_Ioi]; intro t ht; rw [(hFd t ht).deriv]; positivity
  -- F(t) ≤ F(ε) + C t³/3 for 0 < ε ≤ t ≤ 1
  have hH : AntitoneOn (fun x => F x - C * x ^ 3 / 3) (Ioc 0 1) := by
    have hHd : ∀ t ∈ Ioc (0 : ℝ) 1,
        HasDerivAt (fun x => F x - C * x ^ 3 / 3) (t ^ 2 * Real.exp (-ψ t) - C * (3 * t ^ 2) / 3) t := by
      intro t ht
      have := ((hasDerivAt_pow 3 t).const_mul C).div_const 3
      exact (hFd t ht.1).sub (by convert this using 1)
    apply antitoneOn_of_deriv_nonpos (convex_Ioc 0 1)
    · exact fun t ht => (hHd t ht).continuousAt.continuousWithinAt
    · rw [interior_Ioc]
      exact fun t ht => (hHd t (Ioo_subset_Ioc_self ht)).differentiableAt.differentiableWithinAt
    · rw [interior_Ioc]
      intro t ht
      rw [(hHd t (Ioo_subset_Ioc_self ht)).deriv]
      have hle : Real.exp (-ψ t) ≤ C := Real.exp_le_exp.2 (by linarith [hm t ⟨ht.1.le, ht.2.le⟩])
      have : t ^ 2 * Real.exp (-ψ t) ≤ t ^ 2 * C := mul_le_mul_of_nonneg_left hle (by positivity)
      nlinarith
  have hcont0 : ContinuousWithinAt ψ (Ici 0) 0 := hcont 0 (mem_Ici.2 le_rfl)
  -- F ≥ 0 on (0, 1]
  have hF0 : ∀ t ∈ Ioc (0 : ℝ) 1, 0 ≤ F t := by
    intro t ht
    by_contra hneg
    push Not at hneg
    apply blowup (f := fun x => -ψ x) (f' := fun x => -(F x / x ^ 2)) (s0 := t) (δ := -F t) ht.1
      (by linarith) hcont0.neg (fun x hx => (hψd x hx.1).neg)
    intro x hx
    have hFx : F x ≤ F t := hFmono hx.1 ht.1 hx.2
    have hx2 : 0 < x ^ 2 := by have := hx.1; positivity
    rw [div_le_iff₀ hx2]
    have e : -(F x / x ^ 2) * x ^ 2 = -F x := by rw [neg_mul, div_mul_cancel₀ _ hx2.ne']
    rw [e]; linarith
  -- F ≤ C t³/3 on (0, 1]
  have hF1 : ∀ t ∈ Ioc (0 : ℝ) 1, F t ≤ C * t ^ 3 / 3 := by
    intro t ht
    by_contra hbig
    push Not at hbig
    apply blowup (f := ψ) (f' := fun x => F x / x ^ 2) (s0 := t) (δ := F t - C * t ^ 3 / 3) ht.1
      (by linarith) hcont0 (fun x hx => hψd x hx.1)
    intro x hx
    have hH' := hH ⟨hx.1, hx.2.trans ht.2⟩ ht hx.2
    simp only at hH'
    have hx3 : 0 ≤ C * x ^ 3 / 3 := by have := hx.1; positivity
    have hx2 : 0 < x ^ 2 := by have := hx.1; positivity
    rw [div_le_div_iff_of_pos_right hx2]
    linarith
  refine ⟨C, hCpos, fun t ht => ?_⟩
  have ht0 := ht.1
  have ht2 : 0 < t ^ 2 := by positivity
  have hdt : deriv ψ t = F t / t ^ 2 := by simp only [hF]; field_simp
  rw [hdt, abs_div, abs_of_pos ht2, div_le_iff₀ ht2, abs_of_nonneg (hF0 t ht)]
  have := hF1 t ht
  have e : C * t / 3 * t ^ 2 = C * t ^ 3 / 3 := by ring
  rw [e]; exact this

theorem blind_closed (ψ : ℝ → ℝ) (hψ : IsRegularSolution ψ) :
    ∃ x : ℕ → ℝ,
      StrictMono x ∧
      Tendsto x atTop atTop ∧
      (6.4507514 : ℝ) ≤ x 0 ∧ x 0 ≤ 6.4507515 ∧
      (∀ ξ : ℝ, 0 ≤ ξ → ξ ≠ x 0 → mass ψ ξ < mass ψ (x 0)) ∧
      (∀ k : ℕ, ∀ ξ : ℝ, x (2 * k) ≤ ξ → ξ ≠ x (2 * k + 1) →
        mass ψ (x (2 * k + 1)) < mass ψ ξ) ∧
      (∀ k : ℕ, ∀ ξ : ℝ, x (2 * k + 1) ≤ ξ → ξ ≠ x (2 * k + 2) →
        mass ψ ξ < mass ψ (x (2 * k + 2))) ∧
      (∀ k : ℕ, mass ψ (x (2 * k + 1)) < Real.sqrt (2 / Real.pi)) ∧
      (∀ k : ℕ, Real.sqrt (2 / Real.pi) < mass ψ (x (2 * k))) ∧
      Tendsto (mass ψ) atTop (nhds (Real.sqrt (2 / Real.pi))) := by
  obtain ⟨C, hC, hbd⟩ := F_bounds ψ hψ
  obtain ⟨hcont, h0, hd0, hdiff, hode⟩ := hψ
  set w : ℝ → ℝ := fun s => -ψ s with hwdef
  set φ : ℝ → ℝ := fun s => if 0 < s then -deriv ψ s else 0 with hφdef
  have φpos : ∀ s, 0 < s → φ s = -deriv ψ s := fun s hs => by simp only [hφdef, if_pos hs]
  have φ0 : φ 0 = 0 := by simp only [hφdef, lt_irrefl, if_false]
  have hw : ∀ s ∈ Ici (0 : ℝ), HasDerivWithinAt w (φ s) (Ici 0) s := by
    intro s hs
    rcases eq_or_lt_of_le (mem_Ici.1 hs) with h | h
    · subst h; rw [φ0]; have := hd0.neg; rwa [neg_zero] at this
    · rw [φpos s h]; exact (hdiff s h).hasDerivAt.neg.hasDerivWithinAt
  have hφ0 : ContinuousWithinAt φ (Ici 0) 0 := by
    rw [Metric.continuousWithinAt_iff]
    intro ε hε
    refine ⟨min 1 (ε / C), lt_min one_pos (div_pos hε hC), fun x hx hd => ?_⟩
    rw [Real.dist_eq, sub_zero] at hd
    rw [φ0, Real.dist_eq, sub_zero]
    rcases eq_or_lt_of_le (mem_Ici.1 hx) with h | h
    · subst h; rw [φ0]; simpa using hε
    · rw [φpos x h, abs_neg]
      rw [abs_of_pos h] at hd
      have h1 : x ≤ 1 := (lt_of_lt_of_le hd (min_le_left _ _)).le
      have h2 : x < ε / C := lt_of_lt_of_le hd (min_le_right _ _)
      have := hbd x ⟨h, h1⟩
      have : C * x < ε := by rwa [lt_div_iff₀ hC, mul_comm] at h2
      linarith
  have hφ : ∀ s ∈ Ioi (0 : ℝ),
      HasDerivWithinAt φ (-(2 / s * φ s) - Real.exp (w s)) (Ici 0) s := by
    intro s hs
    have hs0 : (0 : ℝ) < s := hs
    have hG := ((hode s hs0).div (hasDerivAt_pow 2 s) (pow_ne_zero 2 hs0.ne')).neg
    have hev : φ =ᶠ[𝓝 s] fun x => -((x ^ 2 * deriv ψ x) / x ^ 2) := by
      filter_upwards [Ioi_mem_nhds hs0] with x hx
      have hx0 : (x : ℝ) ≠ 0 := ne_of_gt hx
      rw [φpos x hx]; field_simp
    have := (hG.congr_of_eventuallyEq hev)
    rw [φpos s hs0]
    refine (this.congr_deriv ?_).hasDerivWithinAt
    simp only [hwdef]; push_cast; field_simp; ring
  have h0' : w 0 = 0 := by simp only [hwdef, h0, neg_zero]
  obtain ⟨ξ, hmono, htend, h1, h2, hmax0, hmin, hmax, hband, hlim⟩ :=
    Work.Math.BonnorEbertAll.bonnor_ebert_all_extrema w φ hw hφ0 hφ h0'
  have hM : ∀ s, 0 ≤ s →
      mass ψ s = s ^ 2 * (-φ s) * Real.exp (w s / 2) / Real.sqrt (4 * Real.pi) := by
    intro s hs
    unfold mass
    have hr : (4 * Real.pi) ^ (-(1 : ℝ) / 2) = (Real.sqrt (4 * Real.pi))⁻¹ := by
      rw [show (-(1 : ℝ) / 2) = -(1 / 2) by ring, Real.rpow_neg (by positivity),
        ← Real.sqrt_eq_rpow]
    rw [hr]
    rcases eq_or_lt_of_le hs with h | h
    · subst h; simp
    · rw [φpos s h]; simp only [hwdef]; rw [div_eq_mul_inv]; ring_nf
  have hξ0 : ∀ k, 0 ≤ ξ k := fun k =>
    le_trans (by norm_num) (h1.trans (hmono.monotone (Nat.zero_le k)))
  refine ⟨ξ, hmono, htend, h1, h2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s hs hne
    rw [hM s hs, hM _ (hξ0 0)]; exact hmax0 s hs hne
  · intro k s hs hne
    rw [hM s ((hξ0 _).trans hs), hM _ (hξ0 _)]; exact hmin k s hs hne
  · intro k s hs hne
    rw [hM s ((hξ0 _).trans hs), hM _ (hξ0 _)]; exact hmax k s hs hne
  · intro k; rw [hM _ (hξ0 _)]; exact (hband k).1
  · intro k; rw [hM _ (hξ0 _)]; exact (hband k).2
  · refine hlim.congr' ?_
    filter_upwards [eventually_ge_atTop 0] with s hs
    exact (hM s hs).symm

end Work.Math.BonnorEbertAllBlindClosed

#print axioms Work.Math.BonnorEbertAllBlindClosed.blind_closed
