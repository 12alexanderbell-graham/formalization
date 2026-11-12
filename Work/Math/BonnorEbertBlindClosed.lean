import Mathlib
import Work.Math.BonnorEbert
import Work.Math.BonnorEbertBlind

/-! Bonnor–Ebert sphere: the blind restatement `Work.Math.BonnorEbertBlind.blind_bonnor_ebert` (two-sided
derivatives of ψ on (0, ∞), ψ and ψ' right-continuous at 0, mass with the rpow (4π)^(−1/2)) closed from the
frozen headline `Work.Math.BonnorEbert.bonnor_ebert_critical` with w = −ψ, φ = −ψ', S = 7. The one-sided
derivative of ψ at 0 comes from the limit of ψ' (`hasDerivWithinAt_Ici_of_tendsto_deriv`). -/

namespace Work.Math.BonnorEbertBlindClosed
open Set Filter Topology Work.Math.BonnorEbertBlind

theorem blind_closed (ψ dψ : ℝ → ℝ) (h : IsRegularIsothermal ψ dψ) :
    ∃ ξ₁ : ℝ, 6.4507514 ≤ ξ₁ ∧ ξ₁ ≤ 6.4507515 ∧
      StrictMonoOn (beMass ψ dψ) (Icc 0 ξ₁) ∧
      StrictAntiOn (beMass ψ dψ) (Icc ξ₁ 7) ∧
      1.1822265 ≤ beMass ψ dψ ξ₁ ∧ beMass ψ dψ ξ₁ ≤ 1.1822266 ∧
      14.042032 ≤ Real.exp (ψ ξ₁) ∧ Real.exp (ψ ξ₁) ≤ 14.042033 := by
  -- the right derivative of ψ at 0
  have hd0 : HasDerivWithinAt ψ 0 (Ici 0) 0 := by
    refine hasDerivWithinAt_Ici_of_tendsto_deriv (s := Ioi 0)
      (fun x hx => (h.hasDeriv x hx).differentiableAt.differentiableWithinAt)
      (h.psi_cont.mono Ioi_subset_Ici_self) self_mem_nhdsWithin ?_
    have e : ∀ᶠ x in 𝓝[>] (0 : ℝ), dψ x = deriv ψ x :=
      eventually_nhdsWithin_of_forall fun x hx => (h.hasDeriv x hx).deriv.symm
    have t : Tendsto dψ (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have := (h.dpsi_cont.mono Ioi_subset_Ici_self).tendsto
      rwa [h.dpsi_zero] at this
    exact t.congr' e
  have hw : ∀ s ∈ Icc (0 : ℝ) 7, HasDerivWithinAt (fun x => -ψ x) (-dψ s) (Icc 0 7) s := by
    intro s hs
    rcases eq_or_lt_of_le hs.1 with h0 | hpos
    · rw [← h0, h.dpsi_zero, neg_zero]
      have := (hd0.mono (Icc_subset_Ici_self : Icc (0 : ℝ) 7 ⊆ Ici 0)).neg
      rwa [neg_zero] at this
    · exact (h.hasDeriv s hpos).neg.hasDerivWithinAt
  have hφ0 : ContinuousWithinAt (fun x => -dψ x) (Icc 0 7) 0 :=
    (h.dpsi_cont.neg).mono Icc_subset_Ici_self
  have hφ : ∀ s ∈ Ioc (0 : ℝ) 7, HasDerivWithinAt (fun x => -dψ x)
      (-(2 / s * (fun x => -dψ x) s) - Real.exp ((fun x => -ψ x) s)) (Icc 0 7) s := by
    intro s hs
    have := (h.hasDeriv2 s hs.1).neg
    exact (this.congr_deriv (by ring)).hasDerivWithinAt
  have h0 : (fun x => -ψ x) 0 = 0 := by simp [h.psi_zero]
  obtain ⟨ξ₁, a1, a2, a3, a4, a5, a6, a7, a8⟩ :=
    Work.Math.BonnorEbert.bonnor_ebert_critical 7 le_rfl (fun x => -ψ x) (fun x => -dψ x) hw hφ0 hφ h0
  have hm : (fun s => s ^ 2 * (-(fun x => -dψ x) s) * Real.exp ((fun x => -ψ x) s / 2) /
      Real.sqrt (4 * Real.pi)) = beMass ψ dψ := by
    funext s
    simp only [beMass, neg_neg]
    have hp : (0 : ℝ) ≤ 4 * Real.pi := by positivity
    rw [Real.rpow_neg hp, ← Real.sqrt_eq_rpow]
    field_simp
  rw [hm] at a3 a4
  simp only [neg_neg] at a7 a8
  refine ⟨ξ₁, a1, a2, a3, a4, ?_, ?_, a7, a8⟩
  · rw [← hm]; simpa using a5
  · rw [← hm]; simpa using a6

end Work.Math.BonnorEbertBlindClosed
