import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.Order.IntermediateValue
import Checked.FSNeg.NBase
import Checked.FSNeg.NSlowInv
import Checked.FSNeg.NUnclamp
import Checked.FalknerSkan.LimitCore

/-! Falkner–Skan adverse pressure gradient with a free scaled coefficient: a reversed-flow trajectory of the clamped field with neither event never meets a clamp, so it solves the unclamped problem. Module `RUnclamp`, promoted from `Work/FSRev/RUnclamp.lean`. -/

namespace Checked.FSRev.RUnclamp
open Set Filter Topology Checked.FSNeg.NBase Checked.FalknerSkan.LimitCore

theorem unclamp_from {K : ℝ} (hK : 0 ≤ K) {a : ℝ} (ha : 1 ≤ a) {f p q : ℝ → ℝ}
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (cl 2 (p η)) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (cl 2 (q η)) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q
      (-(K * cl (max η 0 + 2) (f η) * cl 2 (q η)) + 1 - cl 2 (p η) ^ 2) (Ici 0) η)
    (hfa0 : 0 < f a) (hfa1 : f a < 1) (hpa0 : 0 < p a) (hpa1 : p a < 1)
    (hqa0 : 0 < q a) (hqa1 : q a < 6 / 5)
    (hp1 : ∀ t ∈ Ici a, p t ≤ 1)
    (htouch : ∀ τ, a < τ → p τ = 1 → q τ = 0 → False) :
    ∀ t ∈ Ici a, 0 < p t ∧ p t ≤ 1 ∧ 0 < q t ∧ q t < 2 ∧ 0 < f t ∧ f t ≤ t := by
  have ha0 : (0 : ℝ) ≤ a := by linarith
  have cl_eq := @Checked.FSNeg.NUnclamp.cl_eq
  have conseq : ∀ τ, a ≤ τ → (∀ s ∈ Ico a τ, 0 < q s ∧ q s < 2) →
      (∀ s ∈ Icc a τ, 0 < p s ∧ p s ≤ 1 ∧ 0 ≤ q s ∧ q s ≤ 2 ∧ 0 < f s ∧ f s ≤ s) := by
    intro τ hτ good
    have hpm : MonotoneOn p (Icc a τ) := mono hp ha0 (fun x hx => by
      have := good x ⟨hx.1.le, hx.2⟩
      rw [cl_eq (by linarith) this.2.le]; exact this.1.le)
    have hpge : ∀ s ∈ Icc a τ, 0 < p s := fun s hs => by
      have := hpm ⟨le_rfl, hτ⟩ hs hs.1; linarith
    have hfm : MonotoneOn f (Icc a τ) := mono hf ha0 (fun x hx => by
      have := hpge x ⟨hx.1.le, hx.2.le⟩
      have h1 := hp1 x hx.1.le
      rw [cl_eq (by linarith) (by linarith)]; exact this.le)
    have hgm : MonotoneOn (fun s => s - f s) (Icc a τ) :=
      mono (g' := fun s => 1 - cl 2 (p s))
        (fun η hη => ((hasDerivWithinAt_id η (Ici 0)).sub (hf η hη))) ha0 (fun x hx => by
          have := hpge x ⟨hx.1.le, hx.2.le⟩
          have h1 := hp1 x hx.1.le
          rw [cl_eq (by linarith) (by linarith)]; linarith)
    intro s hs
    have hps := hpge s hs
    have hfs : 0 < f s := by have := hfm ⟨le_rfl, hτ⟩ hs hs.1; linarith
    have hfs2 : f s ≤ s := by
      have := hgm ⟨le_rfl, hτ⟩ hs hs.1; simp only at this; linarith [hs.1]
    have hp1s := hp1 s hs.1
    rcases eq_or_lt_of_le hs.2 with he | hlt
    · rcases eq_or_lt_of_le hs.1 with h0 | hpos
      · rw [← h0]; exact ⟨hpa0, hpa1.le, hqa0.le, by linarith, hfa0, by linarith⟩
      · subst he
        have hqc : ContinuousAt q s := (at_of hq (by linarith)).continuousAt
        refine ⟨hps, hp1s,
          Checked.FSNeg.NSlowInv.ge_of_left hpos hqc (fun x hx => (good x ⟨hx.1.le, hx.2⟩).1.le),
          Checked.FSNeg.NSlowInv.le_of_left hpos hqc (fun x hx => (good x ⟨hx.1.le, hx.2⟩).2.le),
          hfs, hfs2⟩
    · have g := good s ⟨hs.1, hlt⟩
      exact ⟨hps, hp1s, g.1.le, g.2.le, hfs, hfs2⟩
  have main : ∀ T, a ≤ T → ∀ s ∈ Icc a T, 0 < q s ∧ q s < 2 := by
    intro T hT
    by_contra hcon
    push Not at hcon
    set S : Set ℝ := Icc a T ∩ {s | q s ≤ 0 ∨ 2 ≤ q s} with hSdef
    have hqc := cont_of hq (b := T) ha0
    have hSc : IsClosed S := by
      have e2 : IsClosed (Icc a T ∩ q ⁻¹' Iic 0) := hqc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
      have e2' : IsClosed (Icc a T ∩ q ⁻¹' Ici 2) := hqc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
      have : S = (Icc a T ∩ q ⁻¹' Iic 0) ∪ (Icc a T ∩ q ⁻¹' Ici 2) := by
        ext s
        simp only [hSdef, mem_inter_iff, mem_ofPred_eq, mem_union, mem_preimage, mem_Ici, mem_Iic]
        tauto
      rw [this]; exact e2.union e2'
    obtain ⟨s₀, hs₀, hbad⟩ := hcon
    have hne : S.Nonempty := by
      refine ⟨s₀, hs₀, ?_⟩
      simp only [mem_ofPred_eq]
      by_contra hn
      push Not at hn
      exact absurd (hbad hn.1) (not_le.2 hn.2)
    have hbdd : BddBelow S := ⟨a, fun s hs => hs.1.1⟩
    set τ := sInf S with hτ
    have hτS : τ ∈ S := hSc.csInf_mem hne hbdd
    have hτ0 : a ≤ τ := hτS.1.1
    have hτne : τ ≠ a := by
      intro he
      have := hτS.2
      rw [he] at this
      simp only [mem_ofPred_eq] at this
      rcases this with h | h <;> linarith
    have hτpos : a < τ := lt_of_le_of_ne hτ0 (Ne.symm hτne)
    have hτpos' : 0 < τ := by linarith
    have good : ∀ s ∈ Ico a τ, 0 < q s ∧ q s < 2 := by
      intro s hs
      have hsS : s ∉ S := notMem_of_lt_csInf hs.2 hbdd
      have hsI : s ∈ Icc a T := ⟨hs.1, hs.2.le.trans hτS.1.2⟩
      have : ¬ (q s ≤ 0 ∨ 2 ≤ q s) := fun h => hsS ⟨hsI, h⟩
      push Not at this
      exact this
    have C := conseq τ hτ0 good
    have tq : ∀ s ∈ Icc a τ, -(K * cl (max s 0 + 2) (f s) * cl 2 (q s)) + 1 - cl 2 (p s) ^ 2
        = -(K * f s * q s) + 1 - p s ^ 2 := by
      intro s hs
      have hs0 : 0 ≤ s := ha0.trans hs.1
      obtain ⟨c1, c2, c3, c4, c5, c6⟩ := C s hs
      rw [cl_eq (c := max s 0 + 2) (y := f s) (by rw [max_eq_left hs0]; linarith)
          (by rw [max_eq_left hs0]; linarith),
        cl_eq (c := 2) (y := q s) (by linarith) c4, cl_eq (c := 2) (y := p s) (by linarith) (by linarith)]
    have tp : ∀ s ∈ Icc a τ, cl 2 (q s) = q s := fun s hs => by
      obtain ⟨c1, c2, c3, c4, c5, c6⟩ := C s hs; exact cl_eq (by linarith) c4
    have hτI : τ ∈ Icc a τ := ⟨hτ0, le_rfl⟩
    obtain ⟨Cp0, Cp1, Cq0, Cq2, Cf0, Cft⟩ := C τ hτI
    have hqA : HasDerivAt q (-(K * f τ * q τ) + 1 - p τ ^ 2) τ := by
      have := at_of hq hτpos'; rwa [tq τ hτI] at this
    have hH : AntitoneOn (fun s => q s ^ 2 / 2 + p s ^ 3 / 3 - p s) (Icc a τ) :=
      anti (g' := fun s => q s * (-(K * cl (max s 0 + 2) (f s) * cl 2 (q s)) + 1 - cl 2 (p s) ^ 2)
          + (p s ^ 2 - 1) * cl 2 (q s))
        (fun η hη => by
          have h1 := ((hq η hη).pow 2).div_const 2
          have h2 := ((hp η hη).pow 3).div_const 3
          have := (h1.add h2).sub (hp η hη)
          exact this.congr_deriv (by push_cast; ring))
        ha0 (fun x hx => by
          have hx' : x ∈ Icc a τ := ⟨hx.1.le, hx.2.le⟩
          rw [tq x hx', tp x hx']
          obtain ⟨c1, c2, c3, c4, c5, c6⟩ := C x hx'
          have : 0 ≤ K * (f x * q x ^ 2) := mul_nonneg hK (mul_nonneg c5.le (sq_nonneg _))
          nlinarith)
    have hq2 : q τ < 2 := by
      have := hH ⟨le_rfl, hτ0⟩ hτI hτ0
      simp only at this
      have hpa3 : p a ^ 3 / 3 - p a ≤ 0 := by nlinarith [mul_pos hpa0 hpa0]
      have hqa2 : q a ^ 2 < 36 / 25 := by nlinarith
      have hp3 : p τ - p τ ^ 3 / 3 ≤ 2 / 3 := by nlinarith [sq_nonneg (p τ - 1)]
      nlinarith
    have hq0' : 0 < q τ := by
      rcases lt_or_eq_of_le Cq0 with h | h
      · exact h
      · exfalso
        rcases lt_or_eq_of_le Cp1 with hp' | hp'
        · have hd : 0 < -(K * f τ * q τ) + 1 - p τ ^ 2 := by rw [← h]; nlinarith
          exact Checked.FSNeg.NSlowInv.no_touch_from_above hτpos hqA hd h.symm
            (fun s hs => (good s ⟨hs.1.le, hs.2⟩).1)
        · exact htouch τ hτpos hp' h.symm
    rcases hτS.2 with h | h <;> linarith
  intro t ht
  have ht0 : a ≤ t := ht
  have M := main t ht0
  have C := conseq t ht0 (fun s hs => M s ⟨hs.1, hs.2.le⟩) t ⟨ht0, le_rfl⟩
  have Mt := M t ⟨ht0, le_rfl⟩
  exact ⟨C.1, C.2.1, Mt.1, Mt.2, C.2.2.2.2.1, C.2.2.2.2.2⟩

end Checked.FSRev.RUnclamp
