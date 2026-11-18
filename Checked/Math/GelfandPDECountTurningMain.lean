import Checked.Math.GelfandPDECountMain
import Checked.Math.GLamBands
import Checked.Math.BonnorEbertCountMain

/-! Gelfand problem in the three-dimensional ball as a PDE, `GelfandPDECountTurningMain`: the proof route of `Checked.Math.GelfandPDECountTurning.gelfand_pde_radial_count_turning`. `cset_encard`: for a positive parameter the counted set (functions on the closed ball agreeing there with a radial solution) is the image of the radii s ≥ 0 with s² e^{W(s)} equal to the parameter under s ↦ W(s‖x‖) + log(s²/λ), and this map is injective there (distinct radii give distinct centre values), so the two sets have the same `Set.encard` (`Checked.Math.GelfandPDECountMain.profile`, `Checked.Math.GelfandPDEManyMain.radial_global`, `Checked.Math.GelfandPDEManyMain.ne_of_centre`). `main`: `Checked.Math.BonnorEbertCountMain.count_abstract` applied to the branch parameter with the turning sequence of `Checked.Math.GelfandExtrema.gelfand_extrema` and the limit two; the windows of the first minimum and the second maximum from `Checked.Math.GLamBands.bands`; the maxima decrease and the minima increase by the strict extremum properties. No new certificates. Promoted from `Work/Math/GelfandPDECountTurningMain.lean`. -/

namespace Checked.Math.GelfandPDECountTurningMain
open Set Filter Topology InnerProductSpace Laplacian Metric

/-- The counted set: functions on the closed ball that agree there with a radial solution for `lam`. -/
def cset (lam : ℝ) : Set (closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 → ℝ) :=
  {g : closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 → ℝ | ∃ u : EuclideanSpace ℝ (Fin 3) → ℝ,
          (ContDiffOn ℝ 2 u (ball 0 1) ∧ ContinuousOn u (closedBall 0 1) ∧
          (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → u x = 0) ∧
          (∃ h : ℝ → ℝ, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, u x = h ‖x‖) ∧
          (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ u x + lam * Real.exp (u x) = 0)) ∧
          ∀ x : closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, g x = u x}

theorem cset_encard (W Φ : ℝ → ℝ)
    (hw : ∀ s ∈ Ici (0 : ℝ), HasDerivWithinAt W (Φ s) (Ici 0) s)
    (hφ0 : ContinuousWithinAt Φ (Ici 0) 0)
    (hφ : ∀ s ∈ Ioi (0 : ℝ), HasDerivWithinAt Φ (-(2 / s * Φ s) - Real.exp (W s)) (Ici 0) s)
    (h0 : W 0 = 0) (lam : ℝ) (hl : 0 < lam) :
    (cset lam).encard = {s ∈ Ici (0 : ℝ) | s ^ 2 * Real.exp (W s) = lam}.encard := by
  set R := {s ∈ Ici (0 : ℝ) | s ^ 2 * Real.exp (W s) = lam} with hR
  let F : ℝ → closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 → ℝ :=
    fun s x => W (s * ‖(x : EuclideanSpace ℝ (Fin 3))‖) + Real.log (s ^ 2 / lam)
  have Rpos : ∀ s ∈ R, 0 < s := by
    rintro s ⟨hs, hsl⟩
    rcases (mem_Ici.1 hs).lt_or_eq with h | h
    · exact h
    · subst h; simp at hsl; linarith
  have himg : cset lam = F '' R := by
    ext g
    constructor
    · rintro ⟨u, ⟨hu1, hu2, hu3, hu4, hu5⟩, hg⟩
      obtain ⟨k, hk, hkΛ, hku⟩ :=
        Checked.Math.GelfandPDECountMain.profile W Φ hw hφ0 hφ h0 lam hl u hu1 hu2 hu3 hu4 hu5
      refine ⟨k, ⟨mem_Ici.2 hk.le, hkΛ⟩, funext fun x => ?_⟩
      rw [hg x, hku x x.2]
    · rintro ⟨s, hs, rfl⟩
      exact ⟨_, Checked.Math.GelfandPDEManyMain.radial_global W Φ hw hφ0 hφ h0 s lam (Rpos s hs) hl
        hs.2, fun x => rfl⟩
  have hinj : InjOn F R := by
    intro a ha b hb hab
    have hc := congrFun hab ⟨0, mem_closedBall_self zero_le_one⟩
    exact Checked.Math.GelfandPDEManyMain.ne_of_centre W h0 lam a b (Rpos a ha) (Rpos b hb) hl hc
  rw [himg, hinj.encard_image]

theorem main :
    ∃ lamT : ℕ → ℝ,
      3.321992118 ≤ lamT 0 ∧ lamT 0 ≤ 3.321992119 ∧
      1.664155 ≤ lamT 1 ∧ lamT 1 ≤ 1.664157 ∧ 2.10852 ≤ lamT 2 ∧ lamT 2 ≤ 2.10858 ∧
      StrictAnti (fun k : ℕ => lamT (2 * k)) ∧ StrictMono (fun k : ℕ => lamT (2 * k + 1)) ∧
      (∀ k : ℕ, lamT (2 * k + 1) < 2 ∧ 2 < lamT (2 * k)) ∧
      Tendsto lamT atTop (𝓝 2) ∧
      (∀ lam : ℝ, lamT 0 < lam →
        {g : closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 → ℝ | ∃ u : EuclideanSpace ℝ (Fin 3) → ℝ,
          (ContDiffOn ℝ 2 u (ball 0 1) ∧ ContinuousOn u (closedBall 0 1) ∧
          (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → u x = 0) ∧
          (∃ h : ℝ → ℝ, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, u x = h ‖x‖) ∧
          (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ u x + lam * Real.exp (u x) = 0)) ∧
          ∀ x : closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, g x = u x}.encard = 0) ∧
      {g : closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 → ℝ | ∃ u : EuclideanSpace ℝ (Fin 3) → ℝ,
          (ContDiffOn ℝ 2 u (ball 0 1) ∧ ContinuousOn u (closedBall 0 1) ∧
          (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → u x = 0) ∧
          (∃ h : ℝ → ℝ, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, u x = h ‖x‖) ∧
          (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ u x + lamT 0 * Real.exp (u x) = 0)) ∧
          ∀ x : closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, g x = u x}.encard = 1 ∧
      (∀ k : ℕ, ∀ lam : ℝ, lamT (2 * k + 2) < lam → lam < lamT (2 * k) →
        {g : closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 → ℝ | ∃ u : EuclideanSpace ℝ (Fin 3) → ℝ,
          (ContDiffOn ℝ 2 u (ball 0 1) ∧ ContinuousOn u (closedBall 0 1) ∧
          (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → u x = 0) ∧
          (∃ h : ℝ → ℝ, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, u x = h ‖x‖) ∧
          (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ u x + lam * Real.exp (u x) = 0)) ∧
          ∀ x : closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, g x = u x}.encard = ((2 * k + 2 : ℕ) : ℕ∞)) ∧
      (∀ k : ℕ,
        {g : closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 → ℝ | ∃ u : EuclideanSpace ℝ (Fin 3) → ℝ,
          (ContDiffOn ℝ 2 u (ball 0 1) ∧ ContinuousOn u (closedBall 0 1) ∧
          (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → u x = 0) ∧
          (∃ h : ℝ → ℝ, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, u x = h ‖x‖) ∧
          (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ u x + lamT (2 * k + 2) * Real.exp (u x) = 0)) ∧
          ∀ x : closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, g x = u x}.encard = ((2 * k + 3 : ℕ) : ℕ∞)) ∧
      (∀ lam : ℝ, 0 < lam → lam < lamT 1 →
        {g : closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 → ℝ | ∃ u : EuclideanSpace ℝ (Fin 3) → ℝ,
          (ContDiffOn ℝ 2 u (ball 0 1) ∧ ContinuousOn u (closedBall 0 1) ∧
          (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → u x = 0) ∧
          (∃ h : ℝ → ℝ, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, u x = h ‖x‖) ∧
          (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ u x + lam * Real.exp (u x) = 0)) ∧
          ∀ x : closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, g x = u x}.encard = 1) ∧
      (∀ k : ℕ,
        {g : closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 → ℝ | ∃ u : EuclideanSpace ℝ (Fin 3) → ℝ,
          (ContDiffOn ℝ 2 u (ball 0 1) ∧ ContinuousOn u (closedBall 0 1) ∧
          (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → u x = 0) ∧
          (∃ h : ℝ → ℝ, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, u x = h ‖x‖) ∧
          (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ u x + lamT (2 * k + 1) * Real.exp (u x) = 0)) ∧
          ∀ x : closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, g x = u x}.encard = ((2 * k + 2 : ℕ) : ℕ∞)) ∧
      (∀ k : ℕ, ∀ lam : ℝ, lamT (2 * k + 1) < lam → lam < lamT (2 * k + 3) →
        {g : closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 → ℝ | ∃ u : EuclideanSpace ℝ (Fin 3) → ℝ,
          (ContDiffOn ℝ 2 u (ball 0 1) ∧ ContinuousOn u (closedBall 0 1) ∧
          (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → u x = 0) ∧
          (∃ h : ℝ → ℝ, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, u x = h ‖x‖) ∧
          (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ u x + lam * Real.exp (u x) = 0)) ∧
          ∀ x : closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, g x = u x}.encard = ((2 * k + 3 : ℕ) : ℕ∞)) ∧
      {g : closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 → ℝ | ∃ u : EuclideanSpace ℝ (Fin 3) → ℝ,
          (ContDiffOn ℝ 2 u (ball 0 1) ∧ ContinuousOn u (closedBall 0 1) ∧
          (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → u x = 0) ∧
          (∃ h : ℝ → ℝ, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, u x = h ‖x‖) ∧
          (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ u x + 2 * Real.exp (u x) = 0)) ∧
          ∀ x : closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, g x = u x}.encard = ⊤ :=
  by
  obtain ⟨W, Φ, hw, hφ0, hφ, h0⟩ := Checked.Math.BEGlobalExists.exists_global
  obtain ⟨ζ, hmono, htop, hz0lo, hz0hi, hl0lo, hl0hi, hmax0, hmin, hmax, hband, hlim, hinc0, hdec,
    hinc⟩ := Checked.Math.GelfandExtrema.gelfand_extrema W Φ hw hφ0 hφ h0
  obtain ⟨hl1lo, hl1hi, hl2lo, hl2hi⟩ :=
    Checked.Math.GLamBands.bands W Φ hw hφ0 hφ h0 ζ hmono hz0lo hz0hi hinc0 hdec hinc
  set Λ : ℝ → ℝ := fun s => s ^ 2 * Real.exp (W s) with hΛ
  have cW : ContinuousOn W (Ici 0) := fun t ht => (hw t ht).continuousWithinAt
  have cΛ : ContinuousOn Λ (Ici 0) := (continuousOn_id.pow 2).mul cW.rexp
  have Λ0 : Λ 0 = 0 := by simp [hΛ]
  have hz0 : 0 < ζ 0 := by norm_num at hz0lo; linarith
  have Λpos : ∀ s, 0 < s → 0 < Λ s := fun s hs => by simp only [hΛ]; positivity
  have hzpos : ∀ k, 0 < ζ k := fun k => lt_of_lt_of_le hz0 (hmono.monotone (Nat.zero_le k))
  obtain ⟨cA, cB, cC, cD, cE, cF, cG, cH⟩ :=
    Checked.Math.BonnorEbertCountMain.count_abstract Λ ζ 2 two_pos cΛ Λ0 hmono hz0
      (Λpos _ (hzpos 1)) hmax0 hmin hmax hband hinc0 hdec hinc
  have key := fun lam (hl : 0 < lam) => cset_encard W Φ hw hφ0 hφ h0 lam hl
  have lpos : ∀ k, 0 < Λ (ζ k) := fun k => Λpos _ (hzpos k)
  refine ⟨fun k => Λ (ζ k), hl0lo, hl0hi, hl1lo, hl1hi, hl2lo, hl2hi, ?_, ?_, hband, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · refine strictAnti_nat_of_succ_lt fun k => ?_
    rcases k with _ | j
    · exact hmax0 (ζ 2) (hzpos 2).le (hmono.injective.ne (by norm_num))
    · have h := hmax j (ζ (2 * (j + 1) + 2))
        (hmono.monotone (by omega)) (hmono.injective.ne (by omega))
      simpa [show 2 * (j + 1 + 1) = 2 * (j + 1) + 2 by ring, show 2 * j + 2 = 2 * (j + 1) by ring]
        using h
  · refine strictMono_nat_of_lt_succ fun k => ?_
    have h2 := hmin k (ζ (2 * (k + 1) + 1)) (hmono.monotone (by omega))
      (hmono.injective.ne (by omega))
    exact h2
  · exact hlim.comp htop
  · intro lam hl
    exact (key lam (by linarith [lpos 0])).trans (cA lam hl)
  · exact (key _ (lpos 0)).trans cB
  · intro k lam h1 h2
    exact (key lam (by linarith [lpos (2 * k + 2)])).trans (cC k lam h1 h2)
  · intro k
    exact (key _ (lpos _)).trans (cD k)
  · intro lam hl h1
    exact (key lam hl).trans (cE lam hl h1)
  · intro k
    exact (key _ (lpos _)).trans (cF k)
  · intro k lam h1 h2
    exact (key lam (by linarith [lpos (2 * k + 1)])).trans (cG k lam h1 h2)
  · exact (key 2 two_pos).trans cH


end Checked.Math.GelfandPDECountTurningMain
