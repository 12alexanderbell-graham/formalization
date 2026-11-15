import Mathlib
import Work.Math.BonnorEbertMono
import Work.Math.BonnorEbertMonoBlind

/-! Bonnor–Ebert sphere: the blind restatement
`Work.Math.BonnorEbertMonoBlind.blind_bonnor_ebert_mono` (ψ and dψ given, ψ(0) = 0, dψ(0) = 0, ψ has
derivative dψ within [0, ∞) at every ξ ≥ 0, the equation in divergence form (x ↦ x² dψ(x))' = ξ² e^{−ψ ξ}
within [0, ∞) at every ξ ≥ 0; mass (4π)^{−1/2} e^{−ψ/2} ξ² dψ) closed from the frozen headline
`Work.Math.BonnorEbertMono.bonnor_ebert_extrema_monotone` with w = −ψ, φ = −dψ. Continuity of dψ at 0 is
derived: F(x) = x² dψ(x) is continuous on [0, ∞) with F(0) = 0 and 0 ≤ F' ≤ C x² on [0, 1] (C bounds
e^{−ψ} there), so 0 ≤ F(x) ≤ C x³ and |dψ(x)| ≤ C x. Written by run 2026-11-15T0828Z. -/

namespace Work.Math.BonnorEbertMonoBlindClosed
open Set Filter Topology Work.Math.BonnorEbertMonoBlind

theorem blind_closed (ψ dψ : ℝ → ℝ) (h0 : ψ 0 = 0) (hd0 : dψ 0 = 0)
    (hψ : ∀ ξ, 0 ≤ ξ → HasDerivWithinAt ψ (dψ ξ) (Set.Ici 0) ξ)
    (hode : ∀ ξ, 0 ≤ ξ →
      HasDerivWithinAt (fun x => x ^ 2 * dψ x) (ξ ^ 2 * Real.exp (-(ψ ξ))) (Set.Ici 0) ξ) :
    ∃ ξ : ℕ → ℝ,
      StrictMono ξ ∧
      Tendsto ξ atTop atTop ∧
      (6.4507514 : ℝ) ≤ ξ 0 ∧ ξ 0 ≤ (6.4507515 : ℝ) ∧
      (∀ x : ℝ, 0 ≤ x → x ≠ ξ 0 → beMass ψ dψ x < beMass ψ dψ (ξ 0)) ∧
      (∀ k : ℕ, ∀ x : ℝ, ξ (2 * k) ≤ x → x ≠ ξ (2 * k + 1) →
        beMass ψ dψ (ξ (2 * k + 1)) < beMass ψ dψ x) ∧
      (∀ k : ℕ, ∀ x : ℝ, ξ (2 * k + 1) ≤ x → x ≠ ξ (2 * k + 2) →
        beMass ψ dψ x < beMass ψ dψ (ξ (2 * k + 2))) ∧
      (∀ k : ℕ, beMass ψ dψ (ξ (2 * k + 1)) < Real.sqrt (2 / Real.pi) ∧
        Real.sqrt (2 / Real.pi) < beMass ψ dψ (ξ (2 * k))) ∧
      Tendsto (beMass ψ dψ) atTop (nhds (Real.sqrt (2 / Real.pi))) ∧
      StrictMonoOn (beMass ψ dψ) (Set.Icc 0 (ξ 0)) ∧
      (∀ k : ℕ, StrictAntiOn (beMass ψ dψ) (Set.Icc (ξ (2 * k)) (ξ (2 * k + 1)))) ∧
      (∀ k : ℕ, StrictMonoOn (beMass ψ dψ) (Set.Icc (ξ (2 * k + 1)) (ξ (2 * k + 2)))) := by
  set F : ℝ → ℝ := fun x => x ^ 2 * dψ x with hF
  -- a lower bound of ψ on [0, 1]
  have hcont : ContinuousOn ψ (Icc 0 1) := fun x hx =>
    ((hψ x hx.1).continuousWithinAt).mono Icc_subset_Ici_self
  obtain ⟨m, hm⟩ : ∃ m, ∀ x ∈ Icc (0 : ℝ) 1, m ≤ ψ x := by
    obtain ⟨m, hm⟩ := isCompact_Icc.bddBelow_image hcont
    exact ⟨m, fun x hx => hm ⟨x, hx, rfl⟩⟩
  set C := Real.exp (-m) with hC
  have hCpos : 0 < C := Real.exp_pos _
  have hF0 : F 0 = 0 := by simp [hF, hd0]
  have hFd : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt F (t ^ 2 * Real.exp (-(ψ t))) (Icc 0 1) t :=
    fun t ht => (hode t ht.1).mono Icc_subset_Ici_self
  have hFc : ContinuousOn F (Icc 0 1) := fun t ht => (hFd t ht).continuousWithinAt
  have hFmono : MonotoneOn F (Icc 0 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 1) hFc
    · rw [interior_Icc]
      exact fun t ht => ((hFd t (Ioo_subset_Icc_self ht)).hasDerivAt
        (Icc_mem_nhds ht.1 ht.2)).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro t ht
      rw [((hFd t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)).deriv]
      positivity
  have hH : AntitoneOn (fun x => F x - C * x ^ 3) (Icc 0 1) := by
    have hHd : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt (fun x => F x - C * x ^ 3)
        (t ^ 2 * Real.exp (-(ψ t)) - C * (3 * t ^ 2)) (Icc 0 1) t := by
      intro t ht
      have := ((hasDerivAt_pow 3 t).const_mul C).hasDerivWithinAt (s := Icc 0 1)
      exact (hFd t ht).sub (by convert this using 1)
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 1)
    · exact fun t ht => (hHd t ht).continuousWithinAt
    · rw [interior_Icc]
      exact fun t ht => ((hHd t (Ioo_subset_Icc_self ht)).hasDerivAt
        (Icc_mem_nhds ht.1 ht.2)).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro t ht
      rw [((hHd t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)).deriv]
      have hle : Real.exp (-(ψ t)) ≤ C := Real.exp_le_exp.2 (by linarith [hm t ⟨ht.1.le, ht.2.le⟩])
      have : t ^ 2 * Real.exp (-(ψ t)) ≤ t ^ 2 * C := mul_le_mul_of_nonneg_left hle (by positivity)
      nlinarith
  have bnd : ∀ t ∈ Ioc (0 : ℝ) 1, |dψ t| ≤ C * t := by
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2⟩
    have z : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
    have lo : 0 ≤ F t := by have := hFmono z ht' ht.1.le; rwa [hF0] at this
    have hi : F t ≤ C * t ^ 3 := by
      have := hH z ht' ht.1.le; simp only [hF0] at this; linarith
    have ht2 : 0 < t ^ 2 := by have := ht.1; positivity
    have hdt : dψ t = F t / t ^ 2 := by simp only [hF]; rw [mul_div_cancel_left₀ _ ht2.ne']
    rw [hdt, abs_div, abs_of_pos ht2, div_le_iff₀ ht2, abs_of_nonneg lo]
    nlinarith
  -- the headline's hypotheses for w = −ψ, φ = −dψ
  have hw : ∀ s ∈ Ici (0 : ℝ), HasDerivWithinAt (fun x => -ψ x) (-dψ s) (Ici 0) s :=
    fun s hs => (hψ s hs).neg
  have hφ0 : ContinuousWithinAt (fun x => -dψ x) (Ici 0) 0 := by
    apply ContinuousWithinAt.neg
    rw [Metric.continuousWithinAt_iff]
    intro ε hε
    refine ⟨min 1 (ε / (2 * C)), by positivity, fun {x} hx hdx => ?_⟩
    rw [Real.dist_eq, sub_zero] at hdx
    rw [Real.dist_eq, hd0, sub_zero]
    rcases eq_or_lt_of_le (mem_Ici.1 hx) with h | h
    · rw [← h, hd0]; simpa using hε
    · have hx1 : x ≤ 1 := by
        have := lt_of_lt_of_le hdx (min_le_left _ _); rw [abs_of_pos h] at this; linarith
      have hxε : x < ε / (2 * C) := by
        have := lt_of_lt_of_le hdx (min_le_right _ _); rwa [abs_of_pos h] at this
      have := bnd x ⟨h, hx1⟩
      have : C * x < C * (ε / (2 * C)) := mul_lt_mul_of_pos_left hxε hCpos
      have e : C * (ε / (2 * C)) = ε / 2 := by field_simp
      linarith
  have hφ : ∀ s ∈ Ioi (0 : ℝ), HasDerivWithinAt (fun x => -dψ x)
      (-(2 / s * (fun x => -dψ x) s) - Real.exp ((fun x => -ψ x) s)) (Ici 0) s := by
    intro s hs
    have hs0 : (0 : ℝ) < s := hs
    have hFs : HasDerivAt F (s ^ 2 * Real.exp (-(ψ s))) s :=
      (hode s hs0.le).hasDerivAt (Ici_mem_nhds hs0)
    have hq : HasDerivAt (fun x => F x / x ^ 2)
        ((s ^ 2 * Real.exp (-(ψ s)) * s ^ 2 - F s * (↑2 * s ^ (2 - 1))) / (s ^ 2) ^ 2) s :=
      hFs.div (hasDerivAt_pow 2 s) (by positivity)
    have heq : (fun x => F x / x ^ 2) =ᶠ[𝓝 s] dψ := by
      filter_upwards [Ioi_mem_nhds hs0] with x hx
      have : x ≠ 0 := ne_of_gt hx
      simp only [hF]; field_simp
    have hd : HasDerivAt dψ ((s ^ 2 * Real.exp (-(ψ s)) * s ^ 2 - F s * (↑2 * s ^ (2 - 1))) / (s ^ 2) ^ 2)
        s := hq.congr_of_eventuallyEq heq.symm
    refine (hd.neg.congr_deriv ?_).hasDerivWithinAt
    simp only [hF]
    have : s ≠ 0 := hs0.ne'
    field_simp
    ring
  obtain ⟨ξ, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ :=
    Work.Math.BonnorEbertMono.bonnor_ebert_extrema_monotone (fun x => -ψ x) (fun x => -dψ x) hw hφ0 hφ
      (by simp [h0])
  have hM : (fun s => s ^ 2 * (-(fun x => -dψ x) s) * Real.exp ((fun x => -ψ x) s / 2) /
      Real.sqrt (4 * Real.pi)) = beMass ψ dψ := by
    funext s; simp only [beMass, neg_neg]; rw [neg_div]; field_simp
  have hMs : ∀ s, s ^ 2 * (-(fun x => -dψ x) s) * Real.exp ((fun x => -ψ x) s / 2) /
      Real.sqrt (4 * Real.pi) = beMass ψ dψ s := fun s => congrFun hM s
  simp only [hMs] at a5 a6 a7 a8
  rw [hM] at a9 a10 a11 a12
  exact ⟨ξ, a1, a2, a3, a4, fun x hx hne => a5 x hx hne, fun k x hx hne => a6 k x hx hne,
    fun k x hx hne => a7 k x hx hne, a8, a9, a10, a11, a12⟩

end Work.Math.BonnorEbertMonoBlindClosed
