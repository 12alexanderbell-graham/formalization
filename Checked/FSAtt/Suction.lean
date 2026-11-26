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
import Checked.FSSep.SFlow
import Checked.FSNeg.NUnclamp
import Checked.FSAtt.ABase
import Checked.FSAtt.AUnclamp
import Checked.FSNeg.NLimit
import Checked.FSNeg.NRiccati
import Checked.FalknerSkan.FSScale

/-! Falkner–Skan adverse pressure gradient with a free scaled coefficient at least five and suction at the wall: the clamped flow from (C, 0, α), the certified chain shape from that start, and the solution a slow-approach event gives (0 ≤ C ≤ 2 keeps the clamp |f| ≤ t + 2 inactive). Copies of `AFlow`, `AUnclamp.unclamp` and `AAssemble.slow_class` with the start value C in place of 0; written by `runs/2026-11-26T1228Z/scripts/mk_suction.py`. Module `Suction`. -/

namespace Checked.FSAtt.Suction
open Set Filter Topology Checked.FSNeg.NBase Checked.FSSep.SBase Checked.FSSep.SFlow Checked.FSAtt.ABase Checked.FalknerSkan.LimitCore

/-- The certified chain shape from (C, 0, α): every solution of the clamped coefficient-K field on [0, T] from
(C, 0, α) has the event `E`. -/
def ChainC (K C α : ℝ) (E : (ℝ → ℝ × ℝ × ℝ) → Prop) : Prop :=
  ∃ T > 0, ∀ Y : ℝ → ℝ × ℝ × ℝ, (∀ t ∈ Icc 0 T, HasDerivWithinAt Y (vS K t (Y t)) (Icc 0 T) t) →
    Y 0 = (C, 0, α) → E Y

theorem local_sol (K C α T : ℝ) (hT : 0 < T) : ∃ Y : ℝ → ℝ × ℝ × ℝ, Y 0 = (C, 0, α) ∧
    ∀ t ∈ Icc 0 T, HasDerivWithinAt Y (vS K t (Y t)) (Icc 0 T) t := by
  set L : ℝ := 2 * |K| * T + 4 * |K| + 5 with hL
  have hL0 : 0 ≤ L := by positivity
  have hPL : IsPicardLindelof (vS K) (tmin := 0) (tmax := T) ⟨0, le_rfl, hT.le⟩
      (C, (0 : ℝ), α) (Real.toNNReal (L * T)) 0 (Real.toNNReal L)
      (Real.toNNReal (|K| * T + 4 * |K| + 4)) :=
    { lipschitzOnWith := fun t ht => (lip K ht).lipschitzOnWith
      continuousOn := fun x _ => (cont K x).continuousOn
      norm_le := fun t ht p _ => by
        rw [Real.coe_toNNReal _ hL0]; exact norm_le K ht p
      mul_max_le := by
        rw [Real.coe_toNNReal _ hL0, Real.coe_toNNReal _ (by positivity)]
        simp only [NNReal.coe_zero, sub_zero, sub_self]
        rw [max_eq_left hT.le] }
  exact hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀

theorem exists_sol (K C α : ℝ) : ∃ Y : ℝ → ℝ × ℝ × ℝ, Y 0 = (C, 0, α) ∧
    ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt Y (vS K t (Y t)) (Ici 0) t := by
  have hex : ∀ n : ℕ, ∃ Y : ℝ → ℝ × ℝ × ℝ, Y 0 = (C, 0, α) ∧
      ∀ t ∈ Icc 0 ((n : ℝ) + 1), HasDerivWithinAt Y (vS K t (Y t)) (Icc 0 ((n : ℝ) + 1)) t :=
    fun n => local_sol K C α _ (by positivity)
  choose sol hsol0 hsol using hex
  have hag : ∀ k n : ℕ, ∀ s ∈ Icc (0 : ℝ) ((k : ℝ) + 1), s ≤ (n : ℝ) + 1 → sol k s = sol n s := by
    intro k n s hs hsn
    rcases le_total k n with hkn | hnk
    · have hkn' : (k : ℝ) + 1 ≤ (n : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hkn 1
      exact Checked.FSSep.SFlow.unique_right (by positivity) (hsol k)
        (fun t ht => (hsol n t ⟨ht.1, ht.2.trans hkn'⟩).mono (Icc_subset_Icc_right hkn'))
        ((hsol0 k).trans (hsol0 n).symm) hs
    · have hnk' : (n : ℝ) + 1 ≤ (k : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hnk 1
      exact (Checked.FSSep.SFlow.unique_right (by positivity) (hsol n)
        (fun t ht => (hsol k t ⟨ht.1, ht.2.trans hnk'⟩).mono (Icc_subset_Icc_right hnk'))
        ((hsol0 n).trans (hsol0 k).symm) ⟨hs.1, hsn⟩).symm
  refine ⟨fun t => sol (⌈t⌉₊) t, ?_, fun t ht => ?_⟩
  · simp [hsol0]
  · set n := ⌈t⌉₊ with hn
    have htn : t ≤ (n : ℝ) := Nat.le_ceil t
    have hlt : t < (n : ℝ) + 1 := by linarith
    have heq : ∀ s ∈ Ico (0 : ℝ) ((n : ℝ) + 1), sol (⌈s⌉₊) s = sol n s := by
      intro s hs
      refine hag _ n s ⟨hs.1, ?_⟩ hs.2.le
      have := Nat.le_ceil s; linarith
    have hnhds : Ico (0 : ℝ) ((n : ℝ) + 1) ∈ nhdsWithin t (Ici 0) := by
      have : Iio ((n : ℝ) + 1) ∈ nhds t := Iio_mem_nhds hlt
      have h2 := inter_mem_nhdsWithin (Ici (0 : ℝ)) this
      refine Filter.mem_of_superset h2 ?_
      intro s hs; exact ⟨hs.1, hs.2⟩
    have hd := (hsol n t ⟨ht, hlt.le⟩).mono_of_mem_nhdsWithin
      (Filter.mem_of_superset hnhds (fun s hs => ⟨hs.1, hs.2.le⟩))
    have ht0 : sol (⌈t⌉₊) t = sol n t := rfl
    simp only
    rw [ht0]
    refine hd.congr_of_eventuallyEq ?_ (heq t ⟨ht, hlt⟩)
    exact Filter.mem_of_superset hnhds (fun s hs => heq s hs)

/-- The flow of the clamped field from (C, 0, α). -/
noncomputable def flowC (K C α : ℝ) : ℝ → ℝ × ℝ × ℝ := Classical.choose (exists_sol K C α)

theorem flowC_zero (K C α : ℝ) : flowC K C α 0 = (C, 0, α) := (Classical.choose_spec (exists_sol K C α)).1

theorem flowC_deriv (K C α : ℝ) :
    ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt (flowC K C α) (vS K t (flowC K C α t)) (Ici 0) t :=
  (Classical.choose_spec (exists_sol K C α)).2



theorem cl_eqC {c y : ℝ} (h0 : -c ≤ y) (h1 : y ≤ c) : cl c y = y :=
  cl_of_abs_le (abs_le.2 ⟨h0, h1⟩)

theorem unclampC {K : ℝ} (hK5 : 5 ≤ K) {C : ℝ} (hC0 : 0 ≤ C) (hC2 : C ≤ 2) {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 11 / 10) {f p q : ℝ → ℝ}
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (cl 2 (p η)) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (cl 2 (q η)) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q
      (-(K * cl (max η 0 + 2) (f η) * cl 2 (q η)) + 1 - cl 2 (p η) ^ 2) (Ici 0) η)
    (hf0 : f 0 = C) (hp0 : p 0 = 0) (hq0 : q 0 = α)
    {η₀ : ℝ} (hη₀ : 0 < η₀) (hpre : ∀ s ∈ Icc 0 η₀, p s < 1 ∧ 0 < q s)
    (hs1 : 0 ≤ p η₀) (hs2 : q η₀ < 3 * (1 - p η₀)) (hs3 : 11 / 15 < f η₀) :
    ∀ t ∈ Ici (0 : ℝ), 0 ≤ p t ∧ p t < 1 ∧ 0 < q t ∧ q t < 2 ∧ 0 ≤ f t ∧ f t ≤ t + C ∧
      (η₀ ≤ t → q t < 3 * (1 - p t) ∧ 11 / 15 < f t) := by
  have h00 : (0 : ℝ) ≤ 0 := le_rfl
  -- consequences of "no bad point on [0, τ)" on [0, τ]
  have conseq : ∀ τ, 0 ≤ τ → (∀ s ∈ Ico 0 τ, p s < 1 ∧ 0 < q s ∧ q s < 2) →
      (∀ s ∈ Icc 0 τ, 0 ≤ p s ∧ p s ≤ 1 ∧ 0 ≤ q s ∧ q s ≤ 2 ∧ 0 ≤ f s ∧ f s ≤ s + C) := by
    intro τ hτ good
    have hpm : MonotoneOn p (Icc 0 τ) := mono hp h00 (fun x hx => by
      have := good x ⟨hx.1.le, hx.2⟩
      rw [cl_eqC (by linarith) this.2.2.le]; exact this.2.1.le)
    have hpge : ∀ s ∈ Icc 0 τ, 0 ≤ p s := fun s hs => by
      have := hpm ⟨le_rfl, hτ⟩ hs hs.1; rwa [hp0] at this
    have hfm : MonotoneOn f (Icc 0 τ) := mono hf h00 (fun x hx => by
      have g := good x ⟨hx.1.le, hx.2⟩
      have := hpge x ⟨hx.1.le, hx.2.le⟩
      rw [cl_eqC (by linarith) (by linarith)]; exact this)
    have hgm : MonotoneOn (fun s => s - f s) (Icc 0 τ) :=
      mono (g' := fun s => 1 - cl 2 (p s))
        (fun η hη => ((hasDerivWithinAt_id η (Ici 0)).sub (hf η hη))) h00 (fun x hx => by
          have g := good x ⟨hx.1.le, hx.2⟩
          have := hpge x ⟨hx.1.le, hx.2.le⟩
          rw [cl_eqC (by linarith) (by linarith)]; linarith [g.1])
    intro s hs
    have hps := hpge s hs
    have hfs : 0 ≤ f s := by have := hfm ⟨le_rfl, hτ⟩ hs hs.1; rw [hf0] at this; linarith
    have hfs2 : f s ≤ s + C := by
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
      rw [cl_eqC (c := max s 0 + 2) (y := f s) (by rw [max_eq_left hs.1]; linarith)
          (by rw [max_eq_left hs.1]; linarith),
        cl_eqC (c := 2) (y := q s) (by linarith) c4, cl_eqC (c := 2) (y := p s) (by linarith) (by linarith)]
    have tp : ∀ s ∈ Icc 0 τ, cl 2 (q s) = q s := fun s hs => by
      obtain ⟨c1, c2, c3, c4, c5, c6⟩ := C s hs; exact cl_eqC (by linarith) c4
    have tf : ∀ s ∈ Icc 0 τ, cl 2 (p s) = p s := fun s hs => by
      obtain ⟨c1, c2, c3, c4, c5, c6⟩ := C s hs; exact cl_eqC (by linarith) (by linarith)
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



theorem comps (K C α : ℝ) :
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt (fun t => (flowC K C α t).1) (cl 2 (flowC K C α η).2.1) (Ici 0) η) ∧
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt (fun t => (flowC K C α t).2.1) (cl 2 (flowC K C α η).2.2) (Ici 0) η) ∧
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt (fun t => (flowC K C α t).2.2)
      (-(K * cl (max η 0 + 2) (flowC K C α η).1 * cl 2 (flowC K C α η).2.2) + 1 - cl 2 (flowC K C α η).2.1 ^ 2)
      (Ici 0) η) := by
  refine ⟨fun η hη => ?_, fun η hη => ?_, fun η hη => ?_⟩
  · exact (hasFDerivAt_fst.comp_hasDerivWithinAt η (flowC_deriv K C α η hη))
  · exact (hasFDerivAt_fst.comp_hasDerivWithinAt η
      (hasFDerivAt_snd.comp_hasDerivWithinAt η (flowC_deriv K C α η hη)))
  · exact (hasFDerivAt_snd.comp_hasDerivWithinAt η
      (hasFDerivAt_snd.comp_hasDerivWithinAt η (flowC_deriv K C α η hη)))

theorem slow_classC {K : ℝ} (hK5 : 5 ≤ K) {C : ℝ} (hC0 : 0 ≤ C) (hC2 : C ≤ 2) {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 11 / 10) (hS : SlowA (flowC K C α)) :
    ∃ f p q : ℝ → ℝ,
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - (-1 / K) * (1 - p η ^ 2)) (Ici 0) η) ∧
      f 0 = Real.sqrt K * C ∧ p 0 = 0 ∧ q 0 = α / Real.sqrt K ∧ Tendsto p atTop (𝓝 1) ∧
      (∀ η ∈ Ici (0 : ℝ), 0 < q η ∧ 0 ≤ p η ∧ p η ≤ 1) ∧
      (∀ᶠ η in atTop, q η < 3 * (1 - p η)) := by
  obtain ⟨hF, hP, hQ⟩ := comps K C α
  set F := fun t => (flowC K C α t).1
  set P := fun t => (flowC K C α t).2.1
  set Q := fun t => (flowC K C α t).2.2
  have h0 := flowC_zero K C α
  have hF0 : F 0 = C := by simp [F, h0]
  have hP0 : P 0 = 0 := by simp [P, h0]
  have hQ0 : Q 0 = α := by simp [Q, h0]
  obtain ⟨η₀, hη₀, hpre, hs1, hs2, hs3⟩ := hS
  have U := unclampC hK5 hC0 hC2 hα0 hα1 hF hP hQ hF0 hP0 hQ0 hη₀ hpre hs1 hs2 hs3

  -- the true scaled system
  have tF : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt F (P η) (Ici 0) η := fun η hη => by
    have u := U η hη
    have := hF η hη; rwa [cl_eqC (by linarith [u.1]) (by linarith [u.2.1])] at this
  have tP : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt P (Q η) (Ici 0) η := fun η hη => by
    have u := U η hη
    have := hP η hη; rwa [cl_eqC (by linarith [u.2.2.1]) (by linarith [u.2.2.2.1])] at this
  have tQ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt Q (-(K * F η * Q η) + 1 - P η ^ 2) (Ici 0) η :=
    fun η hη => by
    have u := U η hη
    have hη0 : (0 : ℝ) ≤ η := hη
    have := hQ η hη
    rwa [cl_eqC (c := max η 0 + 2) (y := F η) (by rw [max_eq_left hη0]; linarith [u.2.2.2.2.1])
        (by rw [max_eq_left hη0]; linarith [u.2.2.2.2.2.1]),
      cl_eqC (c := 2) (y := Q η) (by linarith [u.2.2.1]) (by linarith [u.2.2.2.1]),
      cl_eqC (c := 2) (y := P η) (by linarith [u.1]) (by linarith [u.2.1])] at this
  have hlim : Tendsto P atTop (𝓝 1) :=
    Checked.FSNeg.NLimit.neg_limit (by linarith : (0 : ℝ) < K) tF tP tQ le_rfl
      (fun η hη => (U η hη).2.2.1) (by rw [hP0]; norm_num) (fun η hη => (U η hη).2.1)
  -- scaling back: c = √K
  have hc : 0 < Real.sqrt K := Real.sqrt_pos.2 (by linarith)
  have hc2 : Real.sqrt K ^ 2 = K := Real.sq_sqrt (by linarith)
  have hc1 : 1 < Real.sqrt K := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_lt_sqrt (by norm_num) (by linarith)
  have tQ' : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt Q (-(K * F η * Q η) - (-1) * (1 - P η ^ 2)) (Ici 0) η :=
    fun η hη => (tQ η hη).congr_deriv (by ring)
  obtain ⟨A, B, C⟩ := Checked.FalknerSkan.FSScale.scale hc tF tP tQ'
  have hm := Checked.FalknerSkan.FSScale.mapsTo_div hc
  refine ⟨fun s => Real.sqrt K * F (s / Real.sqrt K), fun s => P (s / Real.sqrt K),
    fun s => Q (s / Real.sqrt K) / Real.sqrt K, A, B, fun s hs => ?_, by simp [hF0],
    by simp [hP0], by simp [hQ0], Checked.FalknerSkan.FSScale.scale_lim hc hlim, fun s hs => ?_, ?_⟩
  · refine (C s hs).congr_deriv ?_
    field_simp
    rw [hc2]
  · have u := U (s / Real.sqrt K) (hm hs)
    exact ⟨div_pos u.2.2.1 hc, u.1, u.2.1.le⟩
  · filter_upwards [eventually_ge_atTop (η₀ * Real.sqrt K)] with s hs
    have hs' : η₀ ≤ s / Real.sqrt K := by rw [le_div_iff₀ hc]; exact hs
    have hs0 : s / Real.sqrt K ∈ Ici (0 : ℝ) := hη₀.le.trans hs'
    have u := U _ hs0
    have k := (u.2.2.2.2.2.2 hs').1
    rw [div_lt_iff₀ hc]
    have : 0 < 1 - P (s / Real.sqrt K) := by linarith [u.2.1]
    nlinarith

theorem of_chainC {K C α : ℝ} {E : (ℝ → ℝ × ℝ × ℝ) → Prop} (h : ChainC K C α E) : E (flowC K C α) := by
  obtain ⟨T, _, hT⟩ := h
  exact hT (flowC K C α) (fun t ht => (flowC_deriv K C α t ht.1).mono Icc_subset_Ici_self) (flowC_zero K C α)


end Checked.FSAtt.Suction
