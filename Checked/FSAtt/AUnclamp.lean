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

/-! Falkner–Skan adverse pressure gradient with a free scaled coefficient at least five: a slow-approach or no-event trajectory of the clamped field never meets a clamp, so it solves the unclamped problem. Module `AUnclamp`, promoted from `Work/FSAtt/AUnclamp.lean`. -/

namespace Checked.FSAtt.AUnclamp
open Set Filter Topology Checked.FSNeg.NBase Checked.FalknerSkan.LimitCore

theorem cl_eq {c y : ℝ} (h0 : -c ≤ y) (h1 : y ≤ c) : cl c y = y :=
  cl_of_abs_le (abs_le.2 ⟨h0, h1⟩)

theorem unclamp {K : ℝ} (hK5 : 5 ≤ K) {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 11 / 10) {f p q : ℝ → ℝ}
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (cl 2 (p η)) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (cl 2 (q η)) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q
      (-(K * cl (max η 0 + 2) (f η) * cl 2 (q η)) + 1 - cl 2 (p η) ^ 2) (Ici 0) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = 0) (hq0 : q 0 = α)
    {η₀ : ℝ} (hη₀ : 0 < η₀) (hpre : ∀ s ∈ Icc 0 η₀, p s < 1 ∧ 0 < q s)
    (hs1 : 0 ≤ p η₀) (hs2 : q η₀ < 3 * (1 - p η₀)) (hs3 : 11 / 15 < f η₀) :
    ∀ t ∈ Ici (0 : ℝ), 0 ≤ p t ∧ p t < 1 ∧ 0 < q t ∧ q t < 2 ∧ 0 ≤ f t ∧ f t ≤ t ∧
      (η₀ ≤ t → q t < 3 * (1 - p t) ∧ 11 / 15 < f t) := by
  have h00 : (0 : ℝ) ≤ 0 := le_rfl
  -- consequences of "no bad point on [0, τ)" on [0, τ]
  have conseq : ∀ τ, 0 ≤ τ → (∀ s ∈ Ico 0 τ, p s < 1 ∧ 0 < q s ∧ q s < 2) →
      (∀ s ∈ Icc 0 τ, 0 ≤ p s ∧ p s ≤ 1 ∧ 0 ≤ q s ∧ q s ≤ 2 ∧ 0 ≤ f s ∧ f s ≤ s) := by
    intro τ hτ good
    have hpm : MonotoneOn p (Icc 0 τ) := mono hp h00 (fun x hx => by
      have := good x ⟨hx.1.le, hx.2⟩
      rw [cl_eq (by linarith) this.2.2.le]; exact this.2.1.le)
    have hpge : ∀ s ∈ Icc 0 τ, 0 ≤ p s := fun s hs => by
      have := hpm ⟨le_rfl, hτ⟩ hs hs.1; rwa [hp0] at this
    have hfm : MonotoneOn f (Icc 0 τ) := mono hf h00 (fun x hx => by
      have g := good x ⟨hx.1.le, hx.2⟩
      have := hpge x ⟨hx.1.le, hx.2.le⟩
      rw [cl_eq (by linarith) (by linarith)]; exact this)
    have hgm : MonotoneOn (fun s => s - f s) (Icc 0 τ) :=
      mono (g' := fun s => 1 - cl 2 (p s))
        (fun η hη => ((hasDerivWithinAt_id η (Ici 0)).sub (hf η hη))) h00 (fun x hx => by
          have g := good x ⟨hx.1.le, hx.2⟩
          have := hpge x ⟨hx.1.le, hx.2.le⟩
          rw [cl_eq (by linarith) (by linarith)]; linarith [g.1])
    intro s hs
    have hps := hpge s hs
    have hfs : 0 ≤ f s := by have := hfm ⟨le_rfl, hτ⟩ hs hs.1; rwa [hf0] at this
    have hfs2 : f s ≤ s := by
      have := hgm ⟨le_rfl, hτ⟩ hs hs.1; simp only [hf0] at this; linarith
    rcases eq_or_lt_of_le hs.2 with he | hlt
    · -- s = τ: limits from the left (or τ = 0)
      rcases eq_or_lt_of_le hs.1 with h0 | hpos
      · subst h0; rw [hp0, hq0]; exact ⟨le_rfl, by norm_num, hα0.le, by linarith, hfs, hfs2⟩
      · subst he
        have hpc : ContinuousAt p s := (at_of hp hpos).continuousAt
        have hqc : ContinuousAt q s := (at_of hq hpos).continuousAt
        refine ⟨hps, Checked.FSNeg.NSlowInv.le_of_left hpos hpc (fun x hx => (good x ⟨hx.1.le, hx.2⟩).1.le),
          Checked.FSNeg.NSlowInv.ge_of_left hpos hqc (fun x hx => (good x ⟨hx.1.le, hx.2⟩).2.1.le),
          Checked.FSNeg.NSlowInv.le_of_left hpos hqc (fun x hx => (good x ⟨hx.1.le, hx.2⟩).2.2.le), hfs, hfs2⟩
    · have g := good s ⟨hs.1, hlt⟩
      exact ⟨hps, g.1.le, g.2.1.le, g.2.2.le, hfs, hfs2⟩
  have main : ∀ T, 0 ≤ T → ∀ s ∈ Icc 0 T, p s < 1 ∧ 0 < q s ∧ q s < 2 ∧
      (η₀ ≤ s → q s < 3 * (1 - p s) ∧ 11 / 15 < f s) := by
    intro T hT
    by_contra hcon
    push Not at hcon
    set S : Set ℝ := Icc 0 T ∩ {s | 1 ≤ p s ∨ q s ≤ 0 ∨ 2 ≤ q s ∨
      (η₀ ≤ s ∧ (3 * (1 - p s) ≤ q s ∨ f s ≤ 11 / 15))} with hSdef
    have hpc := cont_of hp (b := T) h00
    have hqc := cont_of hq (b := T) h00
    have hfc := cont_of hf (b := T) h00
    have hSc : IsClosed S := by
      have e1 : IsClosed (Icc 0 T ∩ p ⁻¹' Ici 1) := hpc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
      have e2 : IsClosed (Icc 0 T ∩ q ⁻¹' Iic 0) := hqc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
      have e2' : IsClosed (Icc 0 T ∩ q ⁻¹' Ici 2) := hqc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
      have e3 : IsClosed (Icc 0 T ∩ (fun s => q s - 3 * (1 - p s)) ⁻¹' Ici 0) :=
        (hqc.sub (continuousOn_const.mul (continuousOn_const.sub hpc))).preimage_isClosed_of_isClosed
          isClosed_Icc isClosed_Ici
      have e4 : IsClosed (Icc 0 T ∩ f ⁻¹' Iic (11 / 15)) :=
        hfc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
      have : S = (Icc 0 T ∩ p ⁻¹' Ici 1) ∪ (Icc 0 T ∩ q ⁻¹' Iic 0) ∪ (Icc 0 T ∩ q ⁻¹' Ici 2) ∪
          (Ici η₀ ∩ ((Icc 0 T ∩ (fun s => q s - 3 * (1 - p s)) ⁻¹' Ici 0) ∪
            (Icc 0 T ∩ f ⁻¹' Iic (11 / 15)))) := by
        ext s
        simp only [hSdef, mem_inter_iff, mem_ofPred_eq, mem_union, mem_preimage, mem_Ici, mem_Iic,
          sub_nonneg]
        tauto
      rw [this]
      exact ((e1.union e2).union e2').union (isClosed_Ici.inter (e3.union e4))
    obtain ⟨s₀, hs₀, hbad⟩ := hcon
    have hne : S.Nonempty := by
      refine ⟨s₀, hs₀, ?_⟩
      simp only [mem_ofPred_eq]
      by_contra hn
      push Not at hn
      obtain ⟨a1, a2, a3, a4⟩ := hn
      exact absurd (hbad a1 a2 a3) (by
        push Not; intro h; exact a4 h)
    have hbdd : BddBelow S := ⟨0, fun s hs => hs.1.1⟩
    set τ := sInf S with hτ
    have hτS : τ ∈ S := hSc.csInf_mem hne hbdd
    have hτ0 : 0 ≤ τ := hτS.1.1
    have hτne : τ ≠ 0 := by
      intro he
      have := hτS.2
      rw [he] at this
      simp only [mem_ofPred_eq, hp0, hq0] at this
      rcases this with h | h | h | ⟨h, _⟩ <;> linarith
    have hτpos : 0 < τ := lt_of_le_of_ne hτ0 (Ne.symm hτne)
    have good : ∀ s ∈ Ico 0 τ, p s < 1 ∧ 0 < q s ∧ q s < 2 ∧
        (η₀ ≤ s → q s < 3 * (1 - p s) ∧ 11 / 15 < f s) := by
      intro s hs
      have hsS : s ∉ S := notMem_of_lt_csInf hs.2 hbdd
      have hsI : s ∈ Icc 0 T := ⟨hs.1, hs.2.le.trans hτS.1.2⟩
      have : ¬ (1 ≤ p s ∨ q s ≤ 0 ∨ 2 ≤ q s ∨
          (η₀ ≤ s ∧ (3 * (1 - p s) ≤ q s ∨ f s ≤ 11 / 15))) := fun h => hsS ⟨hsI, h⟩
      push Not at this
      exact ⟨this.1, this.2.1, this.2.2.1, fun h => this.2.2.2 h⟩
    have C := conseq τ hτ0 (fun s hs => ⟨(good s hs).1, (good s hs).2.1, (good s hs).2.2.1⟩)
    -- true derivatives on [0, τ]
    have tq : ∀ s ∈ Icc 0 τ, -(K * cl (max s 0 + 2) (f s) * cl 2 (q s)) + 1 - cl 2 (p s) ^ 2
        = -(K * f s * q s) + 1 - p s ^ 2 := by
      intro s hs
      obtain ⟨c1, c2, c3, c4, c5, c6⟩ := C s hs
      rw [cl_eq (c := max s 0 + 2) (y := f s) (by rw [max_eq_left hs.1]; linarith)
          (by rw [max_eq_left hs.1]; linarith),
        cl_eq (c := 2) (y := q s) (by linarith) c4, cl_eq (c := 2) (y := p s) (by linarith) (by linarith)]
    have tp : ∀ s ∈ Icc 0 τ, cl 2 (q s) = q s := fun s hs => by
      obtain ⟨c1, c2, c3, c4, c5, c6⟩ := C s hs; exact cl_eq (by linarith) c4
    have tf : ∀ s ∈ Icc 0 τ, cl 2 (p s) = p s := fun s hs => by
      obtain ⟨c1, c2, c3, c4, c5, c6⟩ := C s hs; exact cl_eq (by linarith) (by linarith)
    have hτI : τ ∈ Icc 0 τ := ⟨hτ0, le_rfl⟩
    obtain ⟨Cp0, Cp1, Cq0, Cq2, Cf0, Cft⟩ := C τ hτI
    have hqA : HasDerivAt q (-(K * f τ * q τ) + 1 - p τ ^ 2) τ := by
      have := at_of hq hτpos; rwa [tq τ hτI] at this
    have hpA : HasDerivAt p (q τ) τ := by
      have := at_of hp hτpos; rwa [tp τ hτI] at this
    -- energy: q τ < 2
    have hH : AntitoneOn (fun s => q s ^ 2 / 2 + p s ^ 3 / 3 - p s) (Icc 0 τ) :=
      anti (g' := fun s => q s * (-(K * cl (max s 0 + 2) (f s) * cl 2 (q s)) + 1 - cl 2 (p s) ^ 2)
          + (p s ^ 2 - 1) * cl 2 (q s))
        (fun η hη => by
          have h1 := ((hq η hη).pow 2).div_const 2
          have h2 := ((hp η hη).pow 3).div_const 3
          have := (h1.add h2).sub (hp η hη)
          exact this.congr_deriv (by push_cast; ring))
        h00 (fun x hx => by
          have hx' : x ∈ Icc 0 τ := ⟨hx.1.le, hx.2.le⟩
          rw [tq x hx', tp x hx']
          obtain ⟨c1, c2, c3, c4, c5, c6⟩ := C x hx'
          have : 0 ≤ f x * q x ^ 2 := mul_nonneg c5 (sq_nonneg _)
          nlinarith)
    have hq2 : q τ < 2 := by
      have := hH ⟨le_rfl, hτ0⟩ hτI hτ0
      simp only [hp0, hq0] at this
      have hp3 : p τ - p τ ^ 3 / 3 ≤ 2 / 3 := by nlinarith [sq_nonneg (p τ - 1)]
      nlinarith
    -- p τ < 1 and q τ > 0
    have hp1 : p τ < 1 := by
      rcases le_or_gt τ η₀ with hle | hgt
      · exact (hpre τ ⟨hτ0, hle⟩).1
      · have hG : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt (fun s => (1 - p s) * Real.exp (3 * s))
            (Real.exp (3 * η) * (3 * (1 - p η) - cl 2 (q η))) (Ici 0) η := by
          intro η hη
          have he : HasDerivWithinAt (fun s => Real.exp (3 * s)) (Real.exp (3 * η) * 3) (Ici 0) η :=
            (((hasDerivAt_id η).const_mul 3).exp.congr_deriv (by simp)).hasDerivWithinAt
          have := ((hp η hη).const_sub 1).mul he
          exact this.congr_deriv (by ring)
        have hGm := mono hG hη₀.le (b := τ) (fun x hx => by
          have hx' : x ∈ Icc 0 τ := ⟨hη₀.le.trans hx.1.le, hx.2.le⟩
          have := ((good x ⟨hx'.1, hx.2⟩).2.2.2 hx.1.le).1
          rw [tp x hx']
          exact mul_nonneg (Real.exp_pos _).le (by linarith))
        have := hGm ⟨le_rfl, hgt.le⟩ ⟨hgt.le, le_rfl⟩ hgt.le
        simp only at this
        have hA : 0 < (1 - p η₀) * Real.exp (3 * η₀) :=
          mul_pos (by linarith [(hpre η₀ ⟨hη₀.le, le_rfl⟩).1]) (Real.exp_pos _)
        have hB := lt_of_lt_of_le hA this
        have := pos_of_mul_pos_left hB (Real.exp_pos _).le
        linarith
    have hq0' : 0 < q τ := by
      rcases le_or_gt τ η₀ with hle | hgt
      · exact (hpre τ ⟨hτ0, hle⟩).2
      · rcases lt_or_eq_of_le Cq0 with h | h
        · exact h
        · exfalso
          have hd : 0 < -(K * f τ * q τ) + 1 - p τ ^ 2 := by rw [← h]; nlinarith
          exact Checked.FSNeg.NSlowInv.no_touch_from_above hτpos hqA hd h.symm
            (fun s hs => (good s ⟨hs.1.le, hs.2⟩).2.1)
    have hlate : η₀ ≤ τ → q τ < 3 * (1 - p τ) ∧ 11 / 15 < f τ := by
      intro hle
      have hfm : MonotoneOn f (Icc 0 τ) := mono hf h00 (fun x hx => by
        have hx' : x ∈ Icc 0 τ := ⟨hx.1.le, hx.2.le⟩
        rw [tf x hx']; exact (C x hx').1)
      have hfτ : 11 / 15 < f τ := lt_of_lt_of_le hs3 (hfm ⟨hη₀.le, hle⟩ hτI hle)
      refine ⟨?_, hfτ⟩
      rcases eq_or_lt_of_le hle with he | hgt
      · rw [← he]; exact hs2
      · have hWA : HasDerivAt (fun s => q s - 3 * (1 - p s))
            ((-(K * f τ * q τ) + 1 - p τ ^ 2) - 3 * (0 - q τ)) τ :=
          hqA.sub (((hasDerivAt_const τ (1 : ℝ)).sub hpA).const_mul 3)
        have hWle : q τ - 3 * (1 - p τ) ≤ 0 :=
          Checked.FSNeg.NSlowInv.le_of_left (g := fun s => q s - 3 * (1 - p s)) hgt hWA.continuousAt
            (fun s hs => by
              have := ((good s ⟨hη₀.le.trans hs.1.le, hs.2⟩).2.2.2 hs.1.le).1; linarith)
        rcases lt_or_eq_of_le hWle with h | h
        · linarith
        · exfalso
          have hqeq : q τ = 3 * (1 - p τ) := by linarith
          have hd : 0 < -((-(K * f τ * q τ) + 1 - p τ ^ 2) - 3 * (0 - q τ)) := by
            rw [hqeq]
            have : (-(K * f τ * (3 * (1 - p τ))) + 1 - p τ ^ 2) - 3 * (0 - 3 * (1 - p τ)) =
                (1 - p τ) * (11 - 3 * K * f τ - (1 - p τ)) := by ring
            rw [this]
            have hKf : 11 / 3 < K * f τ := by nlinarith [mul_le_mul_of_nonneg_right hK5 (show (0 : ℝ) ≤ f τ by linarith)]
            have : 11 - 3 * K * f τ - (1 - p τ) < 0 := by linarith
            nlinarith
          exact Checked.FSNeg.NSlowInv.no_touch_from_above (g := fun s => -(q s - 3 * (1 - p s))) hgt
            hWA.neg hd (by linarith)
            (fun s hs => by
              have := ((good s ⟨hη₀.le.trans hs.1.le, hs.2⟩).2.2.2 hs.1.le).1; linarith)
    rcases hτS.2 with h | h | h | ⟨h1, h | h⟩
    · linarith
    · linarith
    · linarith
    · linarith [(hlate h1).1]
    · linarith [(hlate h1).2]
  intro t ht
  have ht0 : (0 : ℝ) ≤ t := ht
  have M := main t ht0
  have C := conseq t ht0 (fun s hs => by
    have := M s ⟨hs.1, hs.2.le⟩; exact ⟨this.1, this.2.1, this.2.2.1⟩) t ⟨ht0, le_rfl⟩
  have Mt := M t ⟨ht0, le_rfl⟩
  exact ⟨C.1, Mt.1, Mt.2.1, Mt.2.2.1, C.2.2.2.2.1, C.2.2.2.2.2, Mt.2.2.2⟩

/-- A trajectory of the clamped field from (0, 0, α), 0 < α ≤ 11/10, with p ≤ 1 on [0, ∞) and no
touch (p = 1 and q = 0 together at some τ > 0) never meets a clamp: 0 ≤ p ≤ 1, 0 < q < 2,
0 ≤ f ≤ t. -/
theorem unclamp_neither {K : ℝ} (hK5 : 5 ≤ K) {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 11 / 10) {f p q : ℝ → ℝ}
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (cl 2 (p η)) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (cl 2 (q η)) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q
      (-(K * cl (max η 0 + 2) (f η) * cl 2 (q η)) + 1 - cl 2 (p η) ^ 2) (Ici 0) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = 0) (hq0 : q 0 = α)
    (hp1 : ∀ t ∈ Ici (0 : ℝ), p t ≤ 1)
    (htouch : ∀ τ, 0 < τ → p τ = 1 → q τ = 0 → False) :
    ∀ t ∈ Ici (0 : ℝ), 0 ≤ p t ∧ p t ≤ 1 ∧ 0 < q t ∧ q t < 2 ∧ 0 ≤ f t ∧ f t ≤ t := by
  have h00 : (0 : ℝ) ≤ 0 := le_rfl
  have conseq : ∀ τ, 0 ≤ τ → (∀ s ∈ Ico 0 τ, 0 < q s ∧ q s < 2) →
      (∀ s ∈ Icc 0 τ, 0 ≤ p s ∧ p s ≤ 1 ∧ 0 ≤ q s ∧ q s ≤ 2 ∧ 0 ≤ f s ∧ f s ≤ s) := by
    intro τ hτ good
    have hpm : MonotoneOn p (Icc 0 τ) := mono hp h00 (fun x hx => by
      have := good x ⟨hx.1.le, hx.2⟩
      rw [cl_eq (by linarith) this.2.le]; exact this.1.le)
    have hpge : ∀ s ∈ Icc 0 τ, 0 ≤ p s := fun s hs => by
      have := hpm ⟨le_rfl, hτ⟩ hs hs.1; rwa [hp0] at this
    have hfm : MonotoneOn f (Icc 0 τ) := mono hf h00 (fun x hx => by
      have := hpge x ⟨hx.1.le, hx.2.le⟩
      have h1 := hp1 x hx.1.le
      rw [cl_eq (by linarith) (by linarith)]; exact this)
    have hgm : MonotoneOn (fun s => s - f s) (Icc 0 τ) :=
      mono (g' := fun s => 1 - cl 2 (p s))
        (fun η hη => ((hasDerivWithinAt_id η (Ici 0)).sub (hf η hη))) h00 (fun x hx => by
          have := hpge x ⟨hx.1.le, hx.2.le⟩
          have h1 := hp1 x hx.1.le
          rw [cl_eq (by linarith) (by linarith)]; linarith)
    intro s hs
    have hps := hpge s hs
    have hfs : 0 ≤ f s := by have := hfm ⟨le_rfl, hτ⟩ hs hs.1; rwa [hf0] at this
    have hfs2 : f s ≤ s := by
      have := hgm ⟨le_rfl, hτ⟩ hs hs.1; simp only [hf0] at this; linarith
    have hp1s := hp1 s hs.1
    rcases eq_or_lt_of_le hs.2 with he | hlt
    · rcases eq_or_lt_of_le hs.1 with h0 | hpos
      · subst h0; rw [hq0]; exact ⟨hps, hp1s, hα0.le, by linarith, hfs, hfs2⟩
      · subst he
        have hqc : ContinuousAt q s := (at_of hq hpos).continuousAt
        refine ⟨hps, hp1s,
          Checked.FSNeg.NSlowInv.ge_of_left hpos hqc (fun x hx => (good x ⟨hx.1.le, hx.2⟩).1.le),
          Checked.FSNeg.NSlowInv.le_of_left hpos hqc (fun x hx => (good x ⟨hx.1.le, hx.2⟩).2.le),
          hfs, hfs2⟩
    · have g := good s ⟨hs.1, hlt⟩
      exact ⟨hps, hp1s, g.1.le, g.2.le, hfs, hfs2⟩
  have main : ∀ T, 0 ≤ T → ∀ s ∈ Icc 0 T, 0 < q s ∧ q s < 2 := by
    intro T hT
    by_contra hcon
    push Not at hcon
    set S : Set ℝ := Icc 0 T ∩ {s | q s ≤ 0 ∨ 2 ≤ q s} with hSdef
    have hqc := cont_of hq (b := T) h00
    have hSc : IsClosed S := by
      have e2 : IsClosed (Icc 0 T ∩ q ⁻¹' Iic 0) := hqc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
      have e2' : IsClosed (Icc 0 T ∩ q ⁻¹' Ici 2) := hqc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
      have : S = (Icc 0 T ∩ q ⁻¹' Iic 0) ∪ (Icc 0 T ∩ q ⁻¹' Ici 2) := by
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
    have hbdd : BddBelow S := ⟨0, fun s hs => hs.1.1⟩
    set τ := sInf S with hτ
    have hτS : τ ∈ S := hSc.csInf_mem hne hbdd
    have hτ0 : 0 ≤ τ := hτS.1.1
    have hτne : τ ≠ 0 := by
      intro he
      have := hτS.2
      rw [he] at this
      simp only [mem_ofPred_eq, hq0] at this
      rcases this with h | h <;> linarith
    have hτpos : 0 < τ := lt_of_le_of_ne hτ0 (Ne.symm hτne)
    have good : ∀ s ∈ Ico 0 τ, 0 < q s ∧ q s < 2 := by
      intro s hs
      have hsS : s ∉ S := notMem_of_lt_csInf hs.2 hbdd
      have hsI : s ∈ Icc 0 T := ⟨hs.1, hs.2.le.trans hτS.1.2⟩
      have : ¬ (q s ≤ 0 ∨ 2 ≤ q s) := fun h => hsS ⟨hsI, h⟩
      push Not at this
      exact this
    have C := conseq τ hτ0 good
    have tq : ∀ s ∈ Icc 0 τ, -(K * cl (max s 0 + 2) (f s) * cl 2 (q s)) + 1 - cl 2 (p s) ^ 2
        = -(K * f s * q s) + 1 - p s ^ 2 := by
      intro s hs
      obtain ⟨c1, c2, c3, c4, c5, c6⟩ := C s hs
      rw [cl_eq (c := max s 0 + 2) (y := f s) (by rw [max_eq_left hs.1]; linarith)
          (by rw [max_eq_left hs.1]; linarith),
        cl_eq (c := 2) (y := q s) (by linarith) c4, cl_eq (c := 2) (y := p s) (by linarith) (by linarith)]
    have tp : ∀ s ∈ Icc 0 τ, cl 2 (q s) = q s := fun s hs => by
      obtain ⟨c1, c2, c3, c4, c5, c6⟩ := C s hs; exact cl_eq (by linarith) c4
    have hτI : τ ∈ Icc 0 τ := ⟨hτ0, le_rfl⟩
    obtain ⟨Cp0, Cp1, Cq0, Cq2, Cf0, Cft⟩ := C τ hτI
    have hqA : HasDerivAt q (-(K * f τ * q τ) + 1 - p τ ^ 2) τ := by
      have := at_of hq hτpos; rwa [tq τ hτI] at this
    have hH : AntitoneOn (fun s => q s ^ 2 / 2 + p s ^ 3 / 3 - p s) (Icc 0 τ) :=
      anti (g' := fun s => q s * (-(K * cl (max s 0 + 2) (f s) * cl 2 (q s)) + 1 - cl 2 (p s) ^ 2)
          + (p s ^ 2 - 1) * cl 2 (q s))
        (fun η hη => by
          have h1 := ((hq η hη).pow 2).div_const 2
          have h2 := ((hp η hη).pow 3).div_const 3
          have := (h1.add h2).sub (hp η hη)
          exact this.congr_deriv (by push_cast; ring))
        h00 (fun x hx => by
          have hx' : x ∈ Icc 0 τ := ⟨hx.1.le, hx.2.le⟩
          rw [tq x hx', tp x hx']
          obtain ⟨c1, c2, c3, c4, c5, c6⟩ := C x hx'
          have : 0 ≤ f x * q x ^ 2 := mul_nonneg c5 (sq_nonneg _)
          nlinarith)
    have hq2 : q τ < 2 := by
      have := hH ⟨le_rfl, hτ0⟩ hτI hτ0
      simp only [hp0, hq0] at this
      have hp3 : p τ - p τ ^ 3 / 3 ≤ 2 / 3 := by nlinarith [sq_nonneg (p τ - 1)]
      nlinarith
    have hq0' : 0 < q τ := by
      rcases lt_or_eq_of_le Cq0 with h | h
      · exact h
      · exfalso
        rcases lt_or_eq_of_le Cp1 with hp | hp
        · have hd : 0 < -(K * f τ * q τ) + 1 - p τ ^ 2 := by rw [← h]; nlinarith
          exact Checked.FSNeg.NSlowInv.no_touch_from_above hτpos hqA hd h.symm
            (fun s hs => (good s ⟨hs.1.le, hs.2⟩).1)
        · exact htouch τ hτpos hp h.symm
    rcases hτS.2 with h | h <;> linarith
  intro t ht
  have ht0 : (0 : ℝ) ≤ t := ht
  have M := main t ht0
  have C := conseq t ht0 (fun s hs => M s ⟨hs.1, hs.2.le⟩) t ⟨ht0, le_rfl⟩
  have Mt := M t ⟨ht0, le_rfl⟩
  exact ⟨C.1, C.2.1, Mt.1, Mt.2, C.2.2.2.2.1, C.2.2.2.2.2⟩

end Checked.FSAtt.AUnclamp
