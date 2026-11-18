import Checked.Math.GelfandPDECountMain
import Work.Math.GLamBands

/-! Gelfand problem in the three-dimensional ball as a PDE, `GelfandPDECountValuesMain`: the proof route of
`Work.Math.GelfandPDECountValues.gelfand_pde_radial_count_values`. The count proof of
`Checked.Math.GelfandPDECountMain.main` (copied; `reduce`, `profile` reused), with the band ends lam1 = λ(ζ₁) and
lam2 = λ(ζ₂) enclosed by `Work.Math.GLamBands.bands` in place of the bounds against two. -/

namespace Work.Math.GelfandPDECountValuesMain
open Set Filter Topology InnerProductSpace Laplacian Metric Checked.Math.GelfandPDECountMain

theorem main :
    ∃ lamStar lam1 lam2 : ℝ, 3.321992118 ≤ lamStar ∧ lamStar ≤ 3.321992119 ∧
      1.664155 ≤ lam1 ∧ lam1 ≤ 1.664157 ∧ 2.10852 ≤ lam2 ∧ lam2 ≤ 2.10858 ∧
      (∀ lam : ℝ, lamStar < lam → ∀ u : EuclideanSpace ℝ (Fin 3) → ℝ,
        ¬ (ContDiffOn ℝ 2 u (ball 0 1) ∧
          ContinuousOn u (closedBall 0 1) ∧
          (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → u x = 0) ∧
          (∃ g : ℝ → ℝ, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, u x = g ‖x‖) ∧
          (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ u x + lam * Real.exp (u x) = 0))) ∧
      (∃ u : EuclideanSpace ℝ (Fin 3) → ℝ, (ContDiffOn ℝ 2 u (ball 0 1) ∧
          ContinuousOn u (closedBall 0 1) ∧
          (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → u x = 0) ∧
          (∃ g : ℝ → ℝ, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, u x = g ‖x‖) ∧
          (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ u x + lamStar * Real.exp (u x) = 0)) ∧
        ∀ v : EuclideanSpace ℝ (Fin 3) → ℝ, (ContDiffOn ℝ 2 v (ball 0 1) ∧
          ContinuousOn v (closedBall 0 1) ∧
          (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → v x = 0) ∧
          (∃ g : ℝ → ℝ, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, v x = g ‖x‖) ∧
          (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ v x + lamStar * Real.exp (v x) = 0)) →
          ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, v x = u x) ∧
      (∀ lam : ℝ, lam2 < lam → lam < lamStar →
        ∃ u v : EuclideanSpace ℝ (Fin 3) → ℝ, u 0 ≠ v 0 ∧ (ContDiffOn ℝ 2 u (ball 0 1) ∧
          ContinuousOn u (closedBall 0 1) ∧
          (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → u x = 0) ∧
          (∃ g : ℝ → ℝ, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, u x = g ‖x‖) ∧
          (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ u x + lam * Real.exp (u x) = 0)) ∧ (ContDiffOn ℝ 2 v (ball 0 1) ∧
          ContinuousOn v (closedBall 0 1) ∧
          (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → v x = 0) ∧
          (∃ g : ℝ → ℝ, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, v x = g ‖x‖) ∧
          (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ v x + lam * Real.exp (v x) = 0)) ∧
          ∀ f : EuclideanSpace ℝ (Fin 3) → ℝ, (ContDiffOn ℝ 2 f (ball 0 1) ∧
          ContinuousOn f (closedBall 0 1) ∧
          (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → f x = 0) ∧
          (∃ g : ℝ → ℝ, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, f x = g ‖x‖) ∧
          (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ f x + lam * Real.exp (f x) = 0)) →
            (∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, f x = u x) ∨
            (∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, f x = v x)) ∧
      (∀ lam : ℝ, 0 < lam → lam < lam1 →
        ∃ u : EuclideanSpace ℝ (Fin 3) → ℝ, (ContDiffOn ℝ 2 u (ball 0 1) ∧
          ContinuousOn u (closedBall 0 1) ∧
          (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → u x = 0) ∧
          (∃ g : ℝ → ℝ, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, u x = g ‖x‖) ∧
          (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ u x + lam * Real.exp (u x) = 0)) ∧
          ∀ v : EuclideanSpace ℝ (Fin 3) → ℝ, (ContDiffOn ℝ 2 v (ball 0 1) ∧
          ContinuousOn v (closedBall 0 1) ∧
          (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → v x = 0) ∧
          (∃ g : ℝ → ℝ, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, v x = g ‖x‖) ∧
          (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ v x + lam * Real.exp (v x) = 0)) →
            ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, v x = u x) ∧
      (∃ u v : EuclideanSpace ℝ (Fin 3) → ℝ, u 0 ≠ v 0 ∧ (ContDiffOn ℝ 2 u (ball 0 1) ∧
          ContinuousOn u (closedBall 0 1) ∧
          (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → u x = 0) ∧
          (∃ g : ℝ → ℝ, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, u x = g ‖x‖) ∧
          (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ u x + lam1 * Real.exp (u x) = 0)) ∧ (ContDiffOn ℝ 2 v (ball 0 1) ∧
          ContinuousOn v (closedBall 0 1) ∧
          (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → v x = 0) ∧
          (∃ g : ℝ → ℝ, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, v x = g ‖x‖) ∧
          (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ v x + lam1 * Real.exp (v x) = 0)) ∧
          ∀ f : EuclideanSpace ℝ (Fin 3) → ℝ, (ContDiffOn ℝ 2 f (ball 0 1) ∧
          ContinuousOn f (closedBall 0 1) ∧
          (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → f x = 0) ∧
          (∃ g : ℝ → ℝ, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, f x = g ‖x‖) ∧
          (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ f x + lam1 * Real.exp (f x) = 0)) →
            (∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, f x = u x) ∨ (∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, f x = v x)) ∧
      (∃ u v w : EuclideanSpace ℝ (Fin 3) → ℝ, u 0 ≠ v 0 ∧ u 0 ≠ w 0 ∧ v 0 ≠ w 0 ∧
          (ContDiffOn ℝ 2 u (ball 0 1) ∧
          ContinuousOn u (closedBall 0 1) ∧
          (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → u x = 0) ∧
          (∃ g : ℝ → ℝ, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, u x = g ‖x‖) ∧
          (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ u x + lam2 * Real.exp (u x) = 0)) ∧ (ContDiffOn ℝ 2 v (ball 0 1) ∧
          ContinuousOn v (closedBall 0 1) ∧
          (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → v x = 0) ∧
          (∃ g : ℝ → ℝ, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, v x = g ‖x‖) ∧
          (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ v x + lam2 * Real.exp (v x) = 0)) ∧ (ContDiffOn ℝ 2 w (ball 0 1) ∧
          ContinuousOn w (closedBall 0 1) ∧
          (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → w x = 0) ∧
          (∃ g : ℝ → ℝ, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, w x = g ‖x‖) ∧
          (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ w x + lam2 * Real.exp (w x) = 0)) ∧
          ∀ f : EuclideanSpace ℝ (Fin 3) → ℝ, (ContDiffOn ℝ 2 f (ball 0 1) ∧
          ContinuousOn f (closedBall 0 1) ∧
          (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → f x = 0) ∧
          (∃ g : ℝ → ℝ, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, f x = g ‖x‖) ∧
          (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ f x + lam2 * Real.exp (f x) = 0)) →
            (∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, f x = u x) ∨ (∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, f x = v x) ∨ (∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, f x = w x)) := by
  obtain ⟨W, Φ, hw, hφ0, hφ, h0⟩ := Checked.Math.BEGlobalExists.exists_global
  obtain ⟨ζ, hmono, -, hz0lo, hz0hi, hl0lo, hl0hi, hmax0, hminA, hmaxA, hband, -, hinc0, hdecA, hincA⟩ :=
    Checked.Math.GelfandExtrema.gelfand_extrema W Φ hw hφ0 hφ h0
  have hvals := Work.Math.GLamBands.bands W Φ hw hφ0 hφ h0 ζ hmono hz0lo hz0hi hinc0 hdecA hincA
  have hmin := hminA 0
  have hmaxk := hmaxA 0
  have hdec := hdecA 0
  have hb0 := hband 0
  have hb1 := hband 1
  simp only [mul_zero, mul_one, zero_add] at hmin hmaxk hdec hb0 hb1
  set Λ : ℝ → ℝ := fun s => s ^ 2 * Real.exp (W s) with hΛ
  have cW : ContinuousOn W (Ici 0) := fun t ht => (hw t ht).continuousWithinAt
  have cΛ : ContinuousOn Λ (Ici 0) := (continuousOn_id.pow 2).mul cW.rexp
  have hz0 : 0 < ζ 0 := by norm_num at hz0lo; linarith
  have h01 : ζ 0 < ζ 1 := hmono (by norm_num)
  have h12 : ζ 1 < ζ 2 := hmono (by norm_num)
  have Λpos : ∀ s, 0 < s → 0 < Λ s := fun s hs => by simp only [hΛ]; positivity
  have Λ0 : Λ 0 = 0 := by simp [hΛ]
  -- the solution attached to a radius, and the converse
  have solU : ∀ lam s : ℝ, 0 < lam → 0 < s → Λ s = lam →
      ContDiffOn ℝ 2 (fun x : EuclideanSpace ℝ (Fin 3) => W (s * ‖x‖) + Real.log (s ^ 2 / lam))
        (ball 0 1) ∧
      ContinuousOn (fun x : EuclideanSpace ℝ (Fin 3) => W (s * ‖x‖) + Real.log (s ^ 2 / lam))
        (closedBall 0 1) ∧
      (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → W (s * ‖x‖) + Real.log (s ^ 2 / lam) = 0) ∧
      (∃ g : ℝ → ℝ, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1,
        W (s * ‖x‖) + Real.log (s ^ 2 / lam) = g ‖x‖) ∧
      (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1,
        Δ (fun x : EuclideanSpace ℝ (Fin 3) => W (s * ‖x‖) + Real.log (s ^ 2 / lam)) x +
          lam * Real.exp (W (s * ‖x‖) + Real.log (s ^ 2 / lam)) = 0) :=
    fun lam s hl hs hsl => Checked.Math.GelfandPDEManyMain.radial_global W Φ hw hφ0 hφ h0 s lam hs hl hsl
  have neU : ∀ lam a b : ℝ, 0 < lam → 0 < a → 0 < b → a ≠ b →
      W (a * ‖(0 : EuclideanSpace ℝ (Fin 3))‖) + Real.log (a ^ 2 / lam) ≠
        W (b * ‖(0 : EuclideanSpace ℝ (Fin 3))‖) + Real.log (b ^ 2 / lam) :=
    fun lam a b hl ha hb hab h =>
      hab (Checked.Math.GelfandPDEManyMain.ne_of_centre W h0 lam a b ha hb hl h)
  have prof := profile W Φ hw hφ0 hφ h0
  -- root facts
  have below : ∀ s, 0 ≤ s → s ≠ ζ 0 → Λ s < Λ (ζ 0) := fun s hs hne => hmax0 s hs hne
  have left : ∀ lam, 0 < lam → lam < Λ (ζ 0) → ∃ s1 ∈ Ioo 0 (ζ 0), Λ s1 = lam ∧
      ∀ s ∈ Icc 0 (ζ 0), Λ s = lam → s = s1 := by
    intro lam hl hlt
    have c0 : ContinuousOn Λ (Icc 0 (ζ 0)) := cΛ.mono (fun t ht => ht.1)
    obtain ⟨s1, hs1, hs1Λ⟩ := intermediate_value_Ioo hz0.le c0 (show lam ∈ Ioo (Λ 0) (Λ (ζ 0)) from
      ⟨by rw [Λ0]; exact hl, hlt⟩)
    exact ⟨s1, hs1, hs1Λ, fun s hs hsΛ =>
      hinc0.injOn hs (Ioo_subset_Icc_self hs1) (hsΛ.trans hs1Λ.symm)⟩
  have mid : ∀ lam, Λ (ζ 1) < lam → lam < Λ (ζ 0) → ∃ s2 ∈ Ioo (ζ 0) (ζ 1), Λ s2 = lam ∧
      ∀ s ∈ Icc (ζ 0) (ζ 1), Λ s = lam → s = s2 := by
    intro lam hl hlt
    have c0 : ContinuousOn Λ (Icc (ζ 0) (ζ 1)) := cΛ.mono (fun t ht => le_trans hz0.le ht.1)
    obtain ⟨s2, hs2, hs2Λ⟩ := intermediate_value_Ioo' h01.le c0 (show lam ∈ Ioo (Λ (ζ 1)) (Λ (ζ 0)) from
      ⟨hl, hlt⟩)
    exact ⟨s2, hs2, hs2Λ, fun s hs hsΛ =>
      hdec.injOn hs (Ioo_subset_Icc_self hs2) (hsΛ.trans hs2Λ.symm)⟩
  have l1pos : 0 < Λ (ζ 1) := Λpos _ (hz0.trans h01)
  have l1lt : Λ (ζ 1) < 2 := hb0.1
  have l2gt : 2 < Λ (ζ 2) := hb1.2
  have l2lt : Λ (ζ 2) < Λ (ζ 0) := below _ (hz0.trans (h01.trans h12)).le (hmono.injective.ne (by norm_num))
  have l1lt0 : Λ (ζ 1) < Λ (ζ 0) := by linarith
  refine ⟨Λ (ζ 0), Λ (ζ 1), Λ (ζ 2), by simpa [hΛ] using hl0lo, by simpa [hΛ] using hl0hi,
    hvals.1, hvals.2.1, hvals.2.2.1, hvals.2.2.2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- (a) none above
    intro lam hlt u hu
    obtain ⟨hu1, hu2, hu3, hu4, hu5⟩ := hu
    have hl : 0 < lam := by linarith [Λpos _ hz0]
    obtain ⟨k, hk, hkΛ, -⟩ := prof lam hl u hu1 hu2 hu3 hu4 hu5
    have : Λ k ≤ Λ (ζ 0) := by
      rcases eq_or_ne k (ζ 0) with h | h
      · rw [h]
      · exact (below k hk.le h).le
    have : Λ k = lam := hkΛ
    linarith
  · -- (b) exactly one at the maximum
    have hl : 0 < Λ (ζ 0) := Λpos _ hz0
    refine ⟨_, solU (Λ (ζ 0)) (ζ 0) hl hz0 rfl, fun v hv x hx => ?_⟩
    obtain ⟨hv1, hv2, hv3, hv4, hv5⟩ := hv
    obtain ⟨k, hk, hkΛ, hkv⟩ := prof _ hl v hv1 hv2 hv3 hv4 hv5
    have hkz : k = ζ 0 := by
      by_contra h
      have := below k hk.le h
      have : Λ k = Λ (ζ 0) := hkΛ
      linarith
    rw [hkv x hx, hkz]
  · -- (c) exactly two between the second maximum and the maximum
    intro lam hl2 hlt
    have hl : 0 < lam := by linarith
    obtain ⟨s1, hs1, hs1Λ, hs1u⟩ := left lam hl hlt
    obtain ⟨s2, hs2, hs2Λ, hs2u⟩ := mid lam (by linarith) hlt
    have p1 : 0 < s1 := hs1.1
    have p2 : 0 < s2 := hz0.trans hs2.1
    refine ⟨_, _, neU lam s1 s2 hl p1 p2 (by linarith [hs1.2, hs2.1]),
      solU lam s1 hl p1 hs1Λ, solU lam s2 hl p2 hs2Λ, fun f hf => ?_⟩
    obtain ⟨hf1, hf2, hf3, hf4, hf5⟩ := hf
    obtain ⟨k, hk, hkΛ, hkf⟩ := prof lam hl f hf1 hf2 hf3 hf4 hf5
    have hkΛ' : Λ k = lam := hkΛ
    rcases le_or_gt k (ζ 0) with h | h
    · left; intro x hx; rw [hkf x hx, hs1u k ⟨hk.le, h⟩ hkΛ']
    · rcases le_or_gt k (ζ 1) with h' | h'
      · right; intro x hx; rw [hkf x hx, hs2u k ⟨h.le, h'⟩ hkΛ']
      · exfalso
        rcases eq_or_ne k (ζ 2) with he | he
        · rw [he] at hkΛ'; linarith
        · have := hmaxk k h'.le he
          have : Λ k < Λ (ζ 2) := this
          linarith
  · -- (d) exactly one below the first minimum
    intro lam hl hlt
    obtain ⟨s1, hs1, hs1Λ, hs1u⟩ := left lam hl (by linarith)
    refine ⟨_, solU lam s1 hl hs1.1 hs1Λ, fun f hf x hx => ?_⟩
    obtain ⟨hf1, hf2, hf3, hf4, hf5⟩ := hf
    obtain ⟨k, hk, hkΛ, hkf⟩ := prof lam hl f hf1 hf2 hf3 hf4 hf5
    have hkΛ' : Λ k = lam := hkΛ
    rcases le_or_gt k (ζ 0) with h | h
    · rw [hkf x hx, hs1u k ⟨hk.le, h⟩ hkΛ']
    · exfalso
      rcases eq_or_ne k (ζ 1) with he | he
      · rw [he] at hkΛ'; linarith
      · have := hmin k h.le he
        have : Λ (ζ 1) < Λ k := this
        linarith
  · -- (e) exactly two at the first minimum
    have hl := l1pos
    obtain ⟨s1, hs1, hs1Λ, hs1u⟩ := left _ hl l1lt0
    have p1 : 0 < s1 := hs1.1
    have p2 : 0 < ζ 1 := hz0.trans h01
    refine ⟨_, _, neU _ s1 (ζ 1) hl p1 p2 (by linarith [hs1.2]),
      solU _ s1 hl p1 hs1Λ, solU _ (ζ 1) hl p2 rfl, fun f hf => ?_⟩
    obtain ⟨hf1, hf2, hf3, hf4, hf5⟩ := hf
    obtain ⟨k, hk, hkΛ, hkf⟩ := prof _ hl f hf1 hf2 hf3 hf4 hf5
    have hkΛ' : Λ k = Λ (ζ 1) := hkΛ
    rcases le_or_gt k (ζ 0) with h | h
    · left; intro x hx; rw [hkf x hx, hs1u k ⟨hk.le, h⟩ hkΛ']
    · right
      have he : k = ζ 1 := by
        by_contra he
        have := hmin k h.le he
        have : Λ (ζ 1) < Λ k := this
        linarith
      intro x hx; rw [hkf x hx, he]
  · -- (f) exactly three at the second maximum
    have hl : 0 < Λ (ζ 2) := by linarith
    obtain ⟨s1, hs1, hs1Λ, hs1u⟩ := left _ hl l2lt
    obtain ⟨s2, hs2, hs2Λ, hs2u⟩ := mid _ (by linarith) l2lt
    have p1 : 0 < s1 := hs1.1
    have p2 : 0 < s2 := hz0.trans hs2.1
    have p3 : 0 < ζ 2 := hz0.trans (h01.trans h12)
    refine ⟨_, _, _, neU _ s1 s2 hl p1 p2 (by linarith [hs1.2, hs2.1]),
      neU _ s1 (ζ 2) hl p1 p3 (by linarith [hs1.2]),
      neU _ s2 (ζ 2) hl p2 p3 (by linarith [hs2.2]),
      solU _ s1 hl p1 hs1Λ, solU _ s2 hl p2 hs2Λ, solU _ (ζ 2) hl p3 rfl, fun f hf => ?_⟩
    obtain ⟨hf1, hf2, hf3, hf4, hf5⟩ := hf
    obtain ⟨k, hk, hkΛ, hkf⟩ := prof _ hl f hf1 hf2 hf3 hf4 hf5
    have hkΛ' : Λ k = Λ (ζ 2) := hkΛ
    rcases le_or_gt k (ζ 0) with h | h
    · left; intro x hx; rw [hkf x hx, hs1u k ⟨hk.le, h⟩ hkΛ']
    · rcases le_or_gt k (ζ 1) with h' | h'
      · right; left; intro x hx; rw [hkf x hx, hs2u k ⟨h.le, h'⟩ hkΛ']
      · right; right
        have he : k = ζ 2 := by
          by_contra he
          have := hmaxk k h'.le he
          have : Λ k < Λ (ζ 2) := this
          linarith
        intro x hx; rw [hkf x hx, he]

end Work.Math.GelfandPDECountValuesMain
