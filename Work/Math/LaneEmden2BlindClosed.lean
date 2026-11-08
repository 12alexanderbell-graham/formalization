import Mathlib
import Work.Math.LaneEmden2

/-!
# Lane–Emden index 2: the blind restatement closed in Lean

The blind restatement (Sonnet, run 2026-11-08T0228Z, `runs/2026-11-08T0228Z/blind/LaneEmden2Blind.lean`,
statement copied verbatim below) reads "solution" as θ continuous on [0, 5] with θ' given as data,
θ' → 0 at 0⁺, the equation on the open interval (0, 5), and "first zero" as the least zero in [0, 5].
`bridge` turns these into the program's hypotheses on [0, 9/2] (φ = θ' with φ 0 = 0; the right
derivative 0 at the centre from Mathlib's `hasDerivWithinAt_Ici_of_tendsto_deriv`), and the program's
`Work.Math.LaneEmden2.core` gives the conclusion.
-/

namespace Work.Math.LaneEmden2BlindClosed
open Set Filter Topology

theorem bridge (θ θ' : ℝ → ℝ)
    (hcont : ContinuousOn θ (Set.Icc 0 5))
    (hreg : Filter.Tendsto θ' (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (hθ : ∀ ξ ∈ Set.Ioo (0:ℝ) 5, HasDerivAt θ (θ' ξ) ξ)
    (hθ' : ∀ ξ ∈ Set.Ioo (0:ℝ) 5,
      HasDerivAt θ' (-(2 / ξ) * θ' ξ - θ ξ ^ 2) ξ) :
    let φ : ℝ → ℝ := fun ξ => if ξ = 0 then 0 else θ' ξ
    (∀ ξ ∈ Icc (0 : ℝ) (9 / 2), HasDerivWithinAt θ (φ ξ) (Icc 0 (9 / 2)) ξ) ∧
    ContinuousWithinAt φ (Icc 0 (9 / 2)) 0 ∧
    (∀ ξ ∈ Ioc (0 : ℝ) (9 / 2),
      HasDerivWithinAt φ (-(2 / ξ * φ ξ) - θ ξ ^ 2) (Icc 0 (9 / 2)) ξ) := by
  intro φ
  have hev : ∀ ξ : ℝ, ξ ≠ 0 → φ ξ = θ' ξ := fun ξ h => by simp [φ, h]
  have hφθ' : φ =ᶠ[𝓝[>] (0 : ℝ)] θ' :=
    eventually_nhdsWithin_of_forall fun x (hx : (0 : ℝ) < x) => hev x hx.ne'
  refine ⟨fun ξ hξ => ?_, ?_, fun ξ hξ => ?_⟩
  · rcases eq_or_lt_of_le hξ.1 with h | h
    · subst h
      rw [show φ 0 = 0 by simp [φ]]
      have hs : Ioo (0 : ℝ) 5 ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT (by norm_num)
      have hd : HasDerivWithinAt θ 0 (Ici 0) 0 := by
        apply hasDerivWithinAt_Ici_of_tendsto_deriv (s := Ioo 0 5)
        · exact fun x hx => (hθ x hx).differentiableAt.differentiableWithinAt
        · exact (hcont 0 ⟨le_rfl, by norm_num⟩).mono Ioo_subset_Icc_self
        · exact hs
        · apply hreg.congr'
          filter_upwards [hs] with x hx
          exact (hθ x hx).deriv.symm
      exact hd.mono Icc_subset_Ici_self
    · have hx : ξ ∈ Ioo (0 : ℝ) 5 := ⟨h, by linarith [hξ.2]⟩
      rw [hev ξ h.ne']
      exact (hθ ξ hx).hasDerivWithinAt
  · have h1 : ContinuousWithinAt φ (Ioi 0) 0 := by
      show Tendsto φ (𝓝[>] 0) (𝓝 (φ 0))
      rw [show φ 0 = 0 by simp [φ]]
      exact hreg.congr' hφθ'.symm
    exact (continuousWithinAt_Ioi_iff_Ici.1 h1).mono Icc_subset_Ici_self
  · have hx : ξ ∈ Ioo (0 : ℝ) 5 := ⟨hξ.1, by linarith [hξ.2]⟩
    have he : φ =ᶠ[𝓝 ξ] θ' := by
      filter_upwards [lt_mem_nhds hξ.1] with x hx using hev x hx.ne'
    rw [hev ξ hξ.1.ne']
    have := ((hθ' ξ hx).congr_of_eventuallyEq he).hasDerivWithinAt (s := Icc 0 (9 / 2))
    convert this using 1
    ring

theorem blind_laneEmden2 (θ θ' : ℝ → ℝ)
    (hcont : ContinuousOn θ (Set.Icc 0 5))
    (h0 : θ 0 = 1)
    (hreg : Filter.Tendsto θ' (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (hθ : ∀ ξ ∈ Set.Ioo (0:ℝ) 5, HasDerivAt θ (θ' ξ) ξ)
    (hθ' : ∀ ξ ∈ Set.Ioo (0:ℝ) 5,
      HasDerivAt θ' (-(2 / ξ) * θ' ξ - θ ξ ^ 2) ξ) :
    ∃ ξ₁ : ℝ, IsLeast {ξ : ℝ | ξ ∈ Set.Icc (0:ℝ) 5 ∧ θ ξ = 0} ξ₁ ∧
      (4.3528745959 ≤ ξ₁ ∧ ξ₁ ≤ 4.3528745960) ∧
      (2.4110460120 ≤ -ξ₁ ^ 2 * θ' ξ₁ ∧ -ξ₁ ^ 2 * θ' ξ₁ ≤ 2.4110460122) ∧
      (11.402542860 ≤ ξ₁ ^ 3 / (3 * (-ξ₁ ^ 2 * θ' ξ₁)) ∧
        ξ₁ ^ 3 / (3 * (-ξ₁ ^ 2 * θ' ξ₁)) ≤ 11.402542864) := by
  obtain ⟨hθ1, hφ0, hφ⟩ := bridge θ θ' hcont hreg hθ hθ'
  obtain ⟨ξ₁, ha, hb, hz, hpos, hω1, hω2, hc1, hc2⟩ :=
    Work.Math.LaneEmden2.core θ _ hθ1 hφ0 hφ h0
  have hne : ξ₁ ≠ 0 := by intro h; rw [h] at ha; norm_num at ha
  simp only [hne, ite_false] at hω1 hω2 hc1 hc2
  simp only [neg_mul]
  refine ⟨ξ₁, ⟨⟨⟨by linarith, by linarith⟩, hz⟩, fun ξ hξ => ?_⟩, ⟨ha, hb⟩, ⟨hω1, hω2⟩, ⟨hc1, hc2⟩⟩
  by_contra hlt
  rw [not_le] at hlt
  have := hpos ξ ⟨hξ.1.1, hlt⟩
  rw [hξ.2] at this
  exact lt_irrefl _ this

end Work.Math.LaneEmden2BlindClosed
