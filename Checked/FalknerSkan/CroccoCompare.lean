import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
/-! Crocco variables, a cooperative comparison: two curves of the Crocco system of the stagnation-point equations (non-negative coefficient of the product term) with equal F at the start and ordered z there keep the difference of their z at least its starting value on a common range below one. Module `CroccoCompare`, promoted from `Work/FalknerSkan/CroccoCompare.lean`. -/

namespace Checked.FalknerSkan.CroccoCompare
open Set

/-- One window: if z₂ − z₁ ≥ 0 inside (0, s) with s < L, then (z₂ − z₁)(s) ≥ (z₂ − z₁)(0). -/
theorem compare_window {k L : ℝ} (hk : 0 ≤ k) (hL1 : L ≤ 1)
    {z₁ z₂ F₁ F₂ : ℝ → ℝ}
    (hz₁ : ∀ t ∈ Ico 0 L, 0 < z₁ t)
    (cz₁ : ContinuousOn z₁ (Ico 0 L)) (cz₂ : ContinuousOn z₂ (Ico 0 L))
    (cF₁ : ContinuousOn F₁ (Ico 0 L)) (cF₂ : ContinuousOn F₂ (Ico 0 L))
    (dF₁ : ∀ t ∈ Ioo 0 L, HasDerivAt F₁ (t / z₁ t) t)
    (dF₂ : ∀ t ∈ Ioo 0 L, HasDerivAt F₂ (t / z₂ t) t)
    (dz₁ : ∀ t ∈ Ioo 0 L, HasDerivAt z₁ (-(k * F₁ t) - (1 - t ^ 2) / z₁ t) t)
    (dz₂ : ∀ t ∈ Ioo 0 L, HasDerivAt z₂ (-(k * F₂ t) - (1 - t ^ 2) / z₂ t) t)
    (hF0 : F₁ 0 = F₂ 0) {s : ℝ} (hs0 : 0 ≤ s) (hsL : s < L)
    (hpos : ∀ t ∈ Ioo 0 s, z₁ t ≤ z₂ t) :
    z₂ 0 - z₁ 0 ≤ z₂ s - z₁ s := by
  have hsub : Icc 0 s ⊆ Ico 0 L := fun t ht => ⟨ht.1, lt_of_le_of_lt ht.2 hsL⟩
  have hsubI : Ioo 0 s ⊆ Ioo 0 L := fun t ht => ⟨ht.1, lt_trans ht.2 hsL⟩
  -- E = F₂ − F₁ is antitone on [0, s]
  have hEanti : AntitoneOn (fun t => F₂ t - F₁ t) (Icc 0 s) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (f' := fun t => t / z₂ t - t / z₁ t)
      (convex_Icc 0 s) ((cF₂.mono hsub).sub (cF₁.mono hsub))
    · intro t ht
      rw [interior_Icc] at ht ⊢
      exact ((dF₂ t (hsubI ht)).sub (dF₁ t (hsubI ht))).hasDerivWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      have h1 : 0 < z₁ t := hz₁ t ⟨ht.1.le, lt_trans ht.2 hsL⟩
      have h2 : t / z₂ t ≤ t / z₁ t := div_le_div_of_nonneg_left ht.1.le h1 (hpos t ht)
      linarith
  have hE : ∀ t ∈ Icc 0 s, F₂ t - F₁ t ≤ 0 := by
    intro t ht
    have := hEanti ⟨le_refl 0, hs0⟩ ht ht.1
    simp only at this
    linarith
  -- D = z₂ − z₁ is monotone on [0, s]
  have hDmono : MonotoneOn (fun t => z₂ t - z₁ t) (Icc 0 s) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg
      (f' := fun t => (-(k * F₂ t) - (1 - t ^ 2) / z₂ t) - (-(k * F₁ t) - (1 - t ^ 2) / z₁ t))
      (convex_Icc 0 s) ((cz₂.mono hsub).sub (cz₁.mono hsub))
    · intro t ht
      rw [interior_Icc] at ht ⊢
      exact ((dz₂ t (hsubI ht)).sub (dz₁ t (hsubI ht))).hasDerivWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      have h1 : 0 < z₁ t := hz₁ t ⟨ht.1.le, lt_trans ht.2 hsL⟩
      have ht1 : t < 1 := lt_of_lt_of_le (lt_trans ht.2 hsL) hL1
      have hq : 0 ≤ 1 - t ^ 2 := by nlinarith [ht.1]
      have h2 : (1 - t ^ 2) / z₂ t ≤ (1 - t ^ 2) / z₁ t :=
        div_le_div_of_nonneg_left hq h1 (hpos t ht)
      have hEt : F₂ t - F₁ t ≤ 0 := hE t (Ioo_subset_Icc_self ht)
      have h3 : k * F₂ t ≤ k * F₁ t := mul_le_mul_of_nonneg_left (by linarith) hk
      linarith
  exact hDmono ⟨le_refl 0, hs0⟩ ⟨hs0, le_refl s⟩ hs0

/-- Cooperative comparison in Crocco variables (k ≥ 0, range inside [0, 1)). -/
theorem compare {k L : ℝ} (hk : 0 ≤ k) (hL1 : L ≤ 1)
    {z₁ z₂ F₁ F₂ : ℝ → ℝ}
    (hz₁ : ∀ t ∈ Ico 0 L, 0 < z₁ t) (hz₂ : ∀ t ∈ Ico 0 L, 0 < z₂ t)
    (cz₁ : ContinuousOn z₁ (Ico 0 L)) (cz₂ : ContinuousOn z₂ (Ico 0 L))
    (cF₁ : ContinuousOn F₁ (Ico 0 L)) (cF₂ : ContinuousOn F₂ (Ico 0 L))
    (dF₁ : ∀ t ∈ Ioo 0 L, HasDerivAt F₁ (t / z₁ t) t)
    (dF₂ : ∀ t ∈ Ioo 0 L, HasDerivAt F₂ (t / z₂ t) t)
    (dz₁ : ∀ t ∈ Ioo 0 L, HasDerivAt z₁ (-(k * F₁ t) - (1 - t ^ 2) / z₁ t) t)
    (dz₂ : ∀ t ∈ Ioo 0 L, HasDerivAt z₂ (-(k * F₂ t) - (1 - t ^ 2) / z₂ t) t)
    (hF0 : F₁ 0 = F₂ 0) (hlt : z₁ 0 < z₂ 0) :
    ∀ t ∈ Ico 0 L, z₂ 0 - z₁ 0 ≤ z₂ t - z₁ t := by
  -- Step 1: z₂ − z₁ > 0 on [0, L)
  have hposAll : ∀ t ∈ Ico 0 L, 0 < z₂ t - z₁ t := by
    intro t₁ ht₁
    by_contra hneg
    rw [not_lt] at hneg
    set S : Set ℝ := Icc 0 t₁ ∩ (fun t => z₂ t - z₁ t) ⁻¹' Iic 0 with hS
    have hsub : Icc 0 t₁ ⊆ Ico 0 L := fun t ht => ⟨ht.1, lt_of_le_of_lt ht.2 ht₁.2⟩
    have hSc : IsClosed S :=
      ((cz₂.mono hsub).sub (cz₁.mono hsub)).preimage_isClosed_of_isClosed isClosed_Icc
        isClosed_Iic
    have hSne : S.Nonempty := ⟨t₁, ⟨ht₁.1, le_refl t₁⟩, hneg⟩
    have hSbdd : BddBelow S := ⟨0, fun t ht => ht.1.1⟩
    have hτ : sInf S ∈ S := hSc.csInf_mem hSne hSbdd
    have hwin := compare_window hk hL1 hz₁ cz₁ cz₂ cF₁ cF₂ dF₁ dF₂ dz₁ dz₂ hF0
      (s := sInf S) hτ.1.1 (lt_of_le_of_lt hτ.1.2 ht₁.2) (by
        intro t ht
        by_contra hc
        rw [not_le] at hc
        have htS : t ∈ S := ⟨⟨ht.1.le, le_trans ht.2.le hτ.1.2⟩, by
          show z₂ t - z₁ t ≤ 0
          linarith⟩
        have := csInf_le hSbdd htS
        linarith [ht.2])
    have hτ2 : z₂ (sInf S) - z₁ (sInf S) ≤ 0 := hτ.2
    linarith
  -- Step 2
  intro t ht
  exact compare_window hk hL1 hz₁ cz₁ cz₂ cF₁ cF₂ dF₁ dF₂ dz₁ dz₂ hF0 ht.1 ht.2
    (fun u hu => by
      have := hposAll u ⟨hu.1.le, lt_trans hu.2 ht.2⟩
      linarith)

end Checked.FalknerSkan.CroccoCompare
