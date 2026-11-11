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
import Checked.FalknerSkan.LimitCore

/-! Falkner–Skan adverse pressure gradient with a free coefficient K ≥ 5, forward invariance of the lower
slow-approach region of the clamped adverse-sign field `vS K` (threshold 11/15). Run 2026-11-11T1228Z, port of
`Checked/FSNeg/LInv.lean` (K = 10, threshold 11/30). -/

namespace Work.FSRev.RInv
open Set Filter Topology Checked.FSNeg.NBase Checked.FalknerSkan.LimitCore

theorem cl_pos {c y : ℝ} (hc : 0 < c) (hy : 0 < y) : 0 < cl c y := by
  unfold cl; exact lt_max_of_lt_right (lt_min hc hy)

theorem clp {y : ℝ} (h1 : 1 / 3 < y) (h2 : y ≤ 1) : cl 2 y = y :=
  cl_of_abs_le (abs_le.2 ⟨by linarith, by linarith⟩)

theorem clq {x y : ℝ} (h1 : 1 / 3 < x) (h3 : 0 ≤ y) (h4 : y ≤ 3 * (1 - x)) : cl 2 y = y :=
  cl_of_abs_le (abs_le.2 ⟨by linarith, by linarith⟩)

theorem clf {s y : ℝ} (hs : 0 ≤ s) (h5 : 11 / 15 < y) (h6 : y ≤ s + 1) : cl (max s 0 + 2) y = y :=
  cl_of_abs_le (abs_le.2 ⟨by rw [max_eq_left hs]; linarith, by rw [max_eq_left hs]; linarith⟩)

theorem field_eq {K s x y z : ℝ} (hs : 0 ≤ s) (h1 : 1 / 3 < y) (h2 : y ≤ 1) (h3 : 0 ≤ z)
    (h4 : z ≤ 3 * (1 - y)) (h5 : 11 / 15 < x) (h6 : x ≤ s + 1) :
    -(K * cl (max s 0 + 2) x * cl 2 z) + 1 - cl 2 y ^ 2 = -(K * x * z) + 1 - y ^ 2 := by
  rw [clf hs h5 h6, clq h1 h3 h4, clp h1 h2]

theorem slow_inv_cl {K : ℝ} (hK5 : 5 ≤ K) {f p q : ℝ → ℝ}
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (cl 2 (p η)) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (cl 2 (q η)) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q
      (-(K * cl (max η 0 + 2) (f η) * cl 2 (q η)) + 1 - cl 2 (p η) ^ 2) (Ici 0) η)
    {η₀ : ℝ} (hη₀ : 0 ≤ η₀) (h1 : 1 / 3 < p η₀) (h2 : p η₀ < 1) (h3 : 0 < q η₀)
    (h4 : q η₀ < 3 * (1 - p η₀)) (h5 : 11 / 15 < f η₀) (h6 : f η₀ ≤ η₀ + 1) :
    ∀ η ∈ Ici η₀, 1 / 3 < p η ∧ p η < 1 ∧ 0 < q η ∧ q η < 3 * (1 - p η) ∧ 11 / 15 < f η ∧
      f η ≤ η + 1 := by
  have hη₀' : η₀ ∈ Icc η₀ η₀ := ⟨le_rfl, le_rfl⟩
  -- consequences of "no bad point on [η₀, τ)" on [η₀, τ]
  have conseq : ∀ τ, η₀ ≤ τ →
      (∀ s ∈ Ico η₀ τ, p s < 1 ∧ 0 < q s ∧ q s < 3 * (1 - p s) ∧ 11 / 15 < f s) →
      (∀ s ∈ Icc η₀ τ, 1 / 3 < p s ∧ p s ≤ 1 ∧ 0 ≤ q s ∧ q s ≤ 3 * (1 - p s) ∧ 11 / 15 < f s ∧
        f s ≤ s + 1) := by
    intro τ hτ good
    have hpm : MonotoneOn p (Icc η₀ τ) := mono hp hη₀ (fun x hx =>
      (cl_pos two_pos (good x ⟨hx.1.le, hx.2⟩).2.1).le)
    have hpge : ∀ s ∈ Icc η₀ τ, 1 / 3 < p s := fun s hs =>
      lt_of_lt_of_le h1 (hpm ⟨le_rfl, hτ⟩ hs hs.1)
    have hfm : MonotoneOn f (Icc η₀ τ) := mono hf hη₀ (fun x hx => by
      have g := good x ⟨hx.1.le, hx.2⟩
      have := hpge x ⟨hx.1.le, hx.2.le⟩
      rw [clp this g.1.le]; linarith)
    have hgm : MonotoneOn (fun s => s - f s) (Icc η₀ τ) :=
      mono (g' := fun s => 1 - cl 2 (p s))
        (fun η hη => ((hasDerivWithinAt_id η (Ici 0)).sub (hf η hη))) hη₀ (fun x hx => by
          have g := good x ⟨hx.1.le, hx.2⟩
          have := hpge x ⟨hx.1.le, hx.2.le⟩
          rw [clp this g.1.le]; linarith [g.1])
    intro s hs
    have hps := hpge s hs
    have hfs : 11 / 15 < f s := lt_of_lt_of_le h5 (hfm ⟨le_rfl, hτ⟩ hs hs.1)
    have hfs2 : f s ≤ s + 1 := by
      have := hgm ⟨le_rfl, hτ⟩ hs hs.1; simp only at this; linarith
    rcases eq_or_lt_of_le hs.2 with he | hlt
    · rcases eq_or_lt_of_le hs.1 with h0 | hgt
      · subst h0; exact ⟨hps, h2.le, h3.le, h4.le, hfs, hfs2⟩
      · subst he
        have hpos : 0 < s := lt_of_le_of_lt hη₀ hgt
        have hpA := at_of hp hpos
        have hqc : ContinuousAt q s := (at_of hq hpos).continuousAt
        have hWc : ContinuousAt (fun x => q x - 3 * (1 - p x)) s :=
          hqc.sub (continuousAt_const.mul (continuousAt_const.sub hpA.continuousAt))
        have hW := Checked.FSNeg.NSlowInv.le_of_left (c := 0) hgt hWc
          (fun x hx => by have := (good x ⟨hx.1.le, hx.2⟩).2.2.1; linarith)
        refine ⟨hps, Checked.FSNeg.NSlowInv.le_of_left hgt hpA.continuousAt
            (fun x hx => (good x ⟨hx.1.le, hx.2⟩).1.le),
          Checked.FSNeg.NSlowInv.ge_of_left hgt hqc (fun x hx => (good x ⟨hx.1.le, hx.2⟩).2.1.le),
          by linarith, hfs, hfs2⟩
    · have g := good s ⟨hs.1, hlt⟩
      exact ⟨hps, g.1.le, g.2.1.le, g.2.2.1.le, hfs, hfs2⟩
  have main : ∀ T, η₀ ≤ T → ∀ s ∈ Icc η₀ T,
      p s < 1 ∧ 0 < q s ∧ q s < 3 * (1 - p s) ∧ 11 / 15 < f s := by
    intro T hT
    by_contra hcon
    push Not at hcon
    set S : Set ℝ := Icc η₀ T ∩
      {s | 1 ≤ p s ∨ q s ≤ 0 ∨ 3 * (1 - p s) ≤ q s ∨ f s ≤ 11 / 15} with hSdef
    have hpc := cont_of hp (b := T) hη₀
    have hqc := cont_of hq (b := T) hη₀
    have hfc := cont_of hf (b := T) hη₀
    have hSc : IsClosed S := by
      have e1 : IsClosed (Icc η₀ T ∩ p ⁻¹' Ici 1) :=
        hpc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
      have e2 : IsClosed (Icc η₀ T ∩ q ⁻¹' Iic 0) :=
        hqc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
      have e3 : IsClosed (Icc η₀ T ∩ (fun s => q s - 3 * (1 - p s)) ⁻¹' Ici 0) :=
        (hqc.sub (continuousOn_const.mul (continuousOn_const.sub hpc))).preimage_isClosed_of_isClosed
          isClosed_Icc isClosed_Ici
      have e4 : IsClosed (Icc η₀ T ∩ f ⁻¹' Iic (11 / 15)) :=
        hfc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
      have : S = (Icc η₀ T ∩ p ⁻¹' Ici 1) ∪ (Icc η₀ T ∩ q ⁻¹' Iic 0) ∪
          (Icc η₀ T ∩ (fun s => q s - 3 * (1 - p s)) ⁻¹' Ici 0) ∪
          (Icc η₀ T ∩ f ⁻¹' Iic (11 / 15)) := by
        ext s
        simp only [hSdef, mem_inter_iff, mem_ofPred_eq, mem_union, mem_preimage, mem_Ici, mem_Iic,
          sub_nonneg]
        tauto
      rw [this]
      exact ((e1.union e2).union e3).union e4
    obtain ⟨s₀, hs₀, hbad⟩ := hcon
    have hne : S.Nonempty := by
      refine ⟨s₀, hs₀, ?_⟩
      simp only [mem_ofPred_eq]
      by_contra hn
      push Not at hn
      obtain ⟨a1, a2, a3, a4⟩ := hn
      exact absurd (hbad a1 a2 a3) (not_le.2 a4)
    have hbdd : BddBelow S := ⟨η₀, fun s hs => hs.1.1⟩
    set τ := sInf S with hτ
    have hτS : τ ∈ S := hSc.csInf_mem hne hbdd
    have hτ0 : η₀ ≤ τ := hτS.1.1
    have hτT : τ ≤ T := hτS.1.2
    have hτne : τ ≠ η₀ := by
      intro he
      have := hτS.2
      rw [he] at this
      rcases this with h | h | h | h <;> linarith
    have hτlt : η₀ < τ := lt_of_le_of_ne hτ0 (Ne.symm hτne)
    have hτpos : 0 < τ := lt_of_le_of_lt hη₀ hτlt
    have good : ∀ s ∈ Ico η₀ τ, p s < 1 ∧ 0 < q s ∧ q s < 3 * (1 - p s) ∧ 11 / 15 < f s := by
      intro s hs
      have hsS : s ∉ S := notMem_of_lt_csInf hs.2 hbdd
      have hsI : s ∈ Icc η₀ T := ⟨hs.1, hs.2.le.trans hτT⟩
      have : ¬ (1 ≤ p s ∨ q s ≤ 0 ∨ 3 * (1 - p s) ≤ q s ∨ f s ≤ 11 / 15) :=
        fun h => hsS ⟨hsI, h⟩
      push Not at this
      exact this
    have C := conseq τ hτ0 good
    have hτI : τ ∈ Icc η₀ τ := ⟨hτ0, le_rfl⟩
    obtain ⟨Cp0, Cp1, Cq0, Cq3, Cf0, Cf1⟩ := C τ hτI
    have hqA : HasDerivAt q (-(K * f τ * q τ) + 1 - p τ ^ 2) τ := by
      have := at_of hq hτpos
      rwa [field_eq hτpos.le Cp0 Cp1 Cq0 Cq3 Cf0 Cf1] at this
    have hpA : HasDerivAt p (q τ) τ := by
      have := at_of hp hτpos; rwa [clq Cp0 Cq0 Cq3] at this
    -- (1 − p) e^{3η} nondecreasing
    have hG : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt (fun s => (1 - p s) * Real.exp (3 * s))
        (Real.exp (3 * η) * (3 * (1 - p η) - cl 2 (q η))) (Ici 0) η := by
      intro η hη
      have he : HasDerivWithinAt (fun s => Real.exp (3 * s)) (Real.exp (3 * η) * 3) (Ici 0) η :=
        (((hasDerivAt_id η).const_mul 3).exp.congr_deriv (by simp)).hasDerivWithinAt
      have := ((hp η hη).const_sub 1).mul he
      exact this.congr_deriv (by ring)
    have hGm := mono hG hη₀ (b := τ) (fun x hx => by
      have g := good x ⟨hx.1.le, hx.2⟩
      have c := C x ⟨hx.1.le, hx.2.le⟩
      rw [clq c.1 g.2.1.le g.2.2.1.le]
      exact mul_nonneg (Real.exp_pos _).le (by linarith))
    have hpτ1 : p τ < 1 := by
      have := hGm ⟨le_rfl, hτ0⟩ ⟨hτ0, le_rfl⟩ hτ0
      simp only at this
      have hA : 0 < (1 - p η₀) * Real.exp (3 * η₀) := mul_pos (by linarith) (Real.exp_pos _)
      have hB := lt_of_lt_of_le hA this
      have := pos_of_mul_pos_left hB (Real.exp_pos _).le
      linarith
    -- W = q − 3(1 − p) < 0 at τ
    have hWA : HasDerivAt (fun s => q s - 3 * (1 - p s))
        ((-(K * f τ * q τ) + 1 - p τ ^ 2) - 3 * (0 - q τ)) τ :=
      hqA.sub (((hasDerivAt_const τ (1 : ℝ)).sub hpA).const_mul 3)
    have hW : q τ < 3 * (1 - p τ) := by
      rcases lt_or_eq_of_le Cq3 with h | h
      · exact h
      · exfalso
        have hd : 0 < -((-(K * f τ * q τ) + 1 - p τ ^ 2) - 3 * (0 - q τ)) := by
          rw [h]
          have : (-(K * f τ * (3 * (1 - p τ))) + 1 - p τ ^ 2) - 3 * (0 - 3 * (1 - p τ)) =
              (1 - p τ) * (11 - 3 * K * f τ - (1 - p τ)) := by ring
          rw [this]
          have : 11 - 3 * K * f τ - (1 - p τ) < 0 := by nlinarith
          nlinarith
        exact Checked.FSNeg.NSlowInv.no_touch_from_above (g := fun s => -(q s - 3 * (1 - p s)))
          hτlt hWA.neg hd (by linarith)
          (fun s hs => by have := (good s ⟨hs.1.le, hs.2⟩).2.2.1; linarith)
    have hqτ : 0 < q τ := by
      rcases lt_or_eq_of_le Cq0 with h | h
      · exact h
      · exfalso
        have hd : 0 < -(K * f τ * q τ) + 1 - p τ ^ 2 := by rw [← h]; nlinarith
        exact Checked.FSNeg.NSlowInv.no_touch_from_above hτlt hqA hd h.symm
          (fun s hs => (good s ⟨hs.1.le, hs.2⟩).2.1)
    rcases hτS.2 with h | h | h | h <;> linarith
  intro η hη
  have hη' : η₀ ≤ η := hη
  have M := main η hη'
  have Ce := conseq η hη' (fun s hs => M s ⟨hs.1, hs.2.le⟩) η ⟨hη', le_rfl⟩
  have Mt := M η ⟨hη', le_rfl⟩
  exact ⟨Ce.1, Mt.1, Mt.2.1, Mt.2.2.1, Mt.2.2.2, Ce.2.2.2.2.2⟩

end Work.FSRev.RInv
