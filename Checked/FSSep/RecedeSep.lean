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
import Checked.FSSep.SUnclamp
import Checked.FSNeg.NLimit
import Checked.FSNeg.NRiccati
import Checked.FalknerSkan.FSScale

/-! Falkner–Skan separation with the wall receding against the stream: the separation stack (`SFlow`, `SUnclamp`, `SAssemble`, as ported in `BlowSep`) at the start (0, w, 0) of the clamped adverse-sign field, w minus one thousandth. The velocity is negative only near the wall and non-negative from one twentieth on (`early`, `late`), so the stream function stays above minus one thousandth and the corrected energy of `BlowSep` applies; the shooting core takes the two certified chain coefficients as parameters. Written by `runs/2026-11-27T0028Z/scripts/mk_sep_recede.py`. Module `RecedeSep`. -/

namespace Checked.FSSep.RecedeSep
open Set Filter Topology Checked.FSNeg.NBase Checked.FSSep.SBase Checked.FalknerSkan.LimitCore

/-- The lower bound of the stream function along the receding-wall trajectories, minus one thousandth. -/
noncomputable def cS : ℝ := -(1 / 1000)

theorem cS_neg : cS < 0 := by norm_num [cS]
theorem cS_nonneg : -(1 / 1000) ≤ cS := by norm_num [cS]
theorem cS_le : cS ≤ 2 := by norm_num [cS]

/-- The certified chain shape from (0, -(1 / 1000), 0): every solution of the clamped coefficient-K field on [0, T] from
that start has the event `E`. -/
def ChainKR (K : ℝ) (E : (ℝ → ℝ × ℝ × ℝ) → Prop) : Prop :=
  ∃ T > 0, ∀ Y : ℝ → ℝ × ℝ × ℝ, (∀ t ∈ Icc 0 T, HasDerivWithinAt Y (vS K t (Y t)) (Icc 0 T) t) →
    Y 0 = (0, -(1 / 1000), 0) → E Y

/-- A solution on [0, T] for every T > 0. -/
theorem local_sol (K T : ℝ) (hT : 0 < T) : ∃ Y : ℝ → ℝ × ℝ × ℝ, Y 0 = (0, -(1 / 1000), 0) ∧
    ∀ t ∈ Icc 0 T, HasDerivWithinAt Y (vS K t (Y t)) (Icc 0 T) t := by
  set L : ℝ := 2 * |K| * T + 4 * |K| + 5 with hL
  have hL0 : 0 ≤ L := by positivity
  have hPL : IsPicardLindelof (vS K) (tmin := 0) (tmax := T) ⟨0, le_rfl, hT.le⟩
      ((0 : ℝ), (-(1 / 1000) : ℝ), (0 : ℝ)) (Real.toNNReal (L * T)) 0 (Real.toNNReal L)
      (Real.toNNReal (|K| * T + 4 * |K| + 4)) :=
    { lipschitzOnWith := fun t ht => (Checked.FSSep.SFlow.lip K ht).lipschitzOnWith
      continuousOn := fun x _ => (Checked.FSSep.SFlow.cont K x).continuousOn
      norm_le := fun t ht p _ => by
        rw [Real.coe_toNNReal _ hL0]; exact Checked.FSSep.SFlow.norm_le K ht p
      mul_max_le := by
        rw [Real.coe_toNNReal _ hL0, Real.coe_toNNReal _ (by positivity)]
        simp only [NNReal.coe_zero, sub_zero, sub_self]
        rw [max_eq_left hT.le] }
  exact hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀

theorem exists_sol (K : ℝ) : ∃ Y : ℝ → ℝ × ℝ × ℝ, Y 0 = (0, -(1 / 1000), 0) ∧
    ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt Y (vS K t (Y t)) (Ici 0) t := by
  have hex : ∀ n : ℕ, ∃ Y : ℝ → ℝ × ℝ × ℝ, Y 0 = (0, -(1 / 1000), 0) ∧
      ∀ t ∈ Icc 0 ((n : ℝ) + 1), HasDerivWithinAt Y (vS K t (Y t)) (Icc 0 ((n : ℝ) + 1)) t :=
    fun n => local_sol K _ (by positivity)
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

/-- The flow of the clamped coefficient-K field from (0, wall velocity, 0). -/
noncomputable def flowK (K : ℝ) : ℝ → ℝ × ℝ × ℝ := Classical.choose (exists_sol K)

theorem flowK_zero (K : ℝ) : flowK K 0 = (0, -(1 / 1000), 0) := (Classical.choose_spec (exists_sol K)).1

theorem flowK_deriv (K : ℝ) :
    ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt (flowK K) (vS K t (flowK K t)) (Ici 0) t :=
  (Classical.choose_spec (exists_sol K)).2


/-- Continuity of the flow in the coefficient K, uniformly on [0, T]. -/
theorem flowK_cont (T : ℝ) (hT : 0 ≤ T) (K₀ : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ K, |K - K₀| < δ → ∀ t ∈ Icc 0 T, dist (flowK K t) (flowK K₀ t) < ε := by
  set L : ℝ := |K₀| * T + 4 * |K₀| + 4 with hL
  have hL0 : 0 < L := by have := abs_nonneg K₀; positivity
  set E : ℝ := Real.exp (L * T) with hE
  have hE0 : 0 < E := Real.exp_pos _
  set A : ℝ := 2 * (T + 2) * E / L with hA
  have hA0 : 0 < A := by positivity
  refine ⟨ε / A, div_pos hε hA0, fun K hK t ht => ?_⟩
  have hd : ∀ (k : ℝ), ∀ s ∈ Ico (0 : ℝ) T,
      HasDerivWithinAt (flowK k) (vS k s (flowK k s)) (Ici s) s := by
    intro k s hs
    refine (flowK_deriv k s hs.1).mono_of_mem_nhdsWithin ?_
    exact Filter.mem_of_superset self_mem_nhdsWithin (fun u hu => hs.1.trans hu)
  have hc : ∀ k : ℝ, ContinuousOn (flowK k) (Icc 0 T) := fun k s hs =>
    ((flowK_deriv k s hs.1).continuousWithinAt).mono (fun u hu => hu.1)
  have h0 : dist (flowK K 0) (flowK K₀ 0) ≤ 0 := by
    rw [flowK_zero, flowK_zero, dist_self]
  have key := dist_le_of_approx_trajectories_ODE_of_mem (v := vS K₀) (s := fun _ => univ)
    (K := Real.toNNReal L) (εf := |K - K₀| * (2 * (T + 2))) (εg := 0)
    (fun s hs => (Checked.FSSep.SFlow.lip K₀ (Ico_subset_Icc_self hs)).lipschitzOnWith)
    (hc K) (hd K) (fun s hs => Checked.FSSep.SFlow.field_diff (Ico_subset_Icc_self hs) K K₀ _) (fun _ _ => mem_univ _)
    (hc K₀) (hd K₀) (fun s _ => by rw [dist_self]) (fun _ _ => mem_univ _) h0 t ht
  rw [Real.coe_toNNReal _ hL0.le, gronwallBound_of_K_ne_0 hL0.ne'] at key
  simp only [zero_mul, zero_add, add_zero, sub_zero] at key
  have hexp : Real.exp (L * t) ≤ E := by
    rw [hE]; apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left ht.2 hL0.le
  have hB : 0 ≤ |K - K₀| * (2 * (T + 2)) := mul_nonneg (abs_nonneg _) (by linarith)
  have h1 : |K - K₀| * (2 * (T + 2)) / L * (Real.exp (L * t) - 1) ≤ |K - K₀| * A := by
    have : |K - K₀| * (2 * (T + 2)) / L * (Real.exp (L * t) - 1) ≤ |K - K₀| * (2 * (T + 2)) / L * E :=
      mul_le_mul_of_nonneg_left (by linarith) (div_nonneg hB hL0.le)
    refine this.trans (le_of_eq ?_)
    rw [hA]; field_simp
  have h2 : |K - K₀| * A < ε := by
    rw [lt_div_iff₀ hA0] at hK; linarith
  linarith

theorem of_chain {K : ℝ} {E : (ℝ → ℝ × ℝ × ℝ) → Prop} (h : ChainKR K E) : E (flowK K) := by
  obtain ⟨T, _, hT⟩ := h
  exact hT (flowK K) (fun t ht => (flowK_deriv K t ht.1).mono Icc_subset_Ici_self) (flowK_zero K)


/-- The start of a zero-wall-shear trajectory of the clamped field: q > 0 on some (0, δ). -/
theorem start {K : ℝ} {f p q : ℝ → ℝ}
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q
      (-(K * cl (max η 0 + 2) (f η) * cl 2 (q η)) + 1 - cl 2 (p η) ^ 2) (Ici 0) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = -(1 / 1000)) (hq0 : q 0 = 0) : ∃ δ > 0, ∀ s ∈ Ioo 0 δ, 0 < q s := by
  have h := hq 0 (le_refl (0 : ℝ))
  have hv : -(K * cl (max (0 : ℝ) 0 + 2) (f 0) * cl 2 (q 0)) + 1 - cl 2 (p 0) ^ 2 = 999999 / 1000000 := by
    rw [hf0, hp0, hq0]; norm_num [cl]
  rw [hv] at h
  exact Checked.FSSep.SUnclamp.q_pos_start h (by norm_num) hq0

/-- Near a receding wall the velocity turns positive before s = 1/21: while p < 0 on [0, 1/21] the stream function
lies in [-s/1000, 0], so the shear grows at rate at least 99/100 and p(1/21) ≥ -1/1000 + 99/(200·441) > 0. -/
theorem early {K : ℝ} (hK : 0 < K) {f p q : ℝ → ℝ}
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (cl 2 (p η)) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (cl 2 (q η)) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q
      (-(K * cl (max η 0 + 2) (f η) * cl 2 (q η)) + 1 - cl 2 (p η) ^ 2) (Ici 0) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = -(1 / 1000)) (hq0 : q 0 = 0)
    (hpm : MonotoneOn p (Icc 0 (1 / 21)))
    (hb : ∀ s ∈ Icc (0 : ℝ) (1 / 21), 0 ≤ q s ∧ q s ≤ 2) :
    0 ≤ p (1 / 21) := by
  have h00 : (0 : ℝ) ≤ 0 := le_rfl
  have hσ : (0 : ℝ) ≤ 1 / 21 := by norm_num
  have hσI : (1 / 21 : ℝ) ∈ Icc (0 : ℝ) (1 / 21) := ⟨hσ, le_rfl⟩
  by_contra hneg
  push Not at hneg
  have hpI : ∀ s ∈ Icc (0 : ℝ) (1 / 21), -(1 / 1000) ≤ p s ∧ p s < 0 := fun s hs => by
    refine ⟨?_, lt_of_le_of_lt (hpm hs hσI hs.2) hneg⟩
    have := hpm ⟨le_rfl, hσ⟩ hs hs.1
    rw [hp0] at this; exact this
  have ceq := @Checked.FSSep.SUnclamp.cl_eq
  have hfa : AntitoneOn f (Icc 0 (1 / 21)) := anti hf h00 (fun x hx => by
    have := hpI x ⟨hx.1.le, hx.2.le⟩
    rw [ceq (by linarith) (by linarith)]; exact this.2.le)
  have hfle : ∀ s ∈ Icc (0 : ℝ) (1 / 21), f s ≤ 0 := fun s hs => by
    have := hfa ⟨le_rfl, hσ⟩ hs hs.1; rwa [hf0] at this
  have hfd : MonotoneOn (fun s => f s + 1 / 1000 * s) (Icc 0 (1 / 21)) :=
    mono (g' := fun s => cl 2 (p s) + 1 / 1000 * 1)
      (fun η hη => (hf η hη).add ((hasDerivWithinAt_id η (Ici 0)).const_mul (1 / 1000))) h00
      (fun x hx => by
        have := hpI x ⟨hx.1.le, hx.2.le⟩
        rw [ceq (by linarith) (by linarith)]; linarith [this.1])
  have hfge : ∀ s ∈ Icc (0 : ℝ) (1 / 21), -(1 / 1000) * s ≤ f s := fun s hs => by
    have := hfd ⟨le_rfl, hσ⟩ hs hs.1
    dsimp only at this; rw [hf0] at this; linarith
  have hqm : MonotoneOn (fun s => q s - 99 / 100 * s) (Icc 0 (1 / 21)) :=
    mono (g' := fun s => (-(K * cl (max s 0 + 2) (f s) * cl 2 (q s)) + 1 - cl 2 (p s) ^ 2) - 99 / 100 * 1)
      (fun η hη => (hq η hη).sub ((hasDerivWithinAt_id η (Ici 0)).const_mul (99 / 100))) h00
      (fun x hx => by
        have hx' : x ∈ Icc (0 : ℝ) (1 / 21) := ⟨hx.1.le, hx.2.le⟩
        obtain ⟨a1, a2⟩ := hpI x hx'
        obtain ⟨b1, b2⟩ := hb x hx'
        have c1 := hfle x hx'
        have c2 := hfge x hx'
        rw [ceq (c := max x 0 + 2) (y := f x) (by rw [max_eq_left hx'.1]; linarith)
            (by rw [max_eq_left hx'.1]; linarith),
          ceq (c := 2) (y := q x) (by linarith) b2, ceq (c := 2) (y := p x) (by linarith) (by linarith)]
        have e : 0 ≤ K * (-f x) * q x := mul_nonneg (mul_nonneg hK.le (by linarith)) b1
        have hp2 : p x ^ 2 ≤ 1 / 1000000 := by nlinarith
        nlinarith)
  have hqge : ∀ s ∈ Icc (0 : ℝ) (1 / 21), 99 / 100 * s ≤ q s := fun s hs => by
    have := hqm ⟨le_rfl, hσ⟩ hs hs.1
    dsimp only at this; rw [hq0] at this; linarith
  have hpm2 : MonotoneOn (fun s => p s - 99 / 200 * (s * s)) (Icc 0 (1 / 21)) :=
    mono (g' := fun s => cl 2 (q s) - 99 / 200 * (1 * s + s * 1))
      (fun η hη => (hp η hη).sub
        (((hasDerivWithinAt_id η (Ici 0)).mul (hasDerivWithinAt_id η (Ici 0))).const_mul (99 / 200))) h00
      (fun x hx => by
        have hx' : x ∈ Icc (0 : ℝ) (1 / 21) := ⟨hx.1.le, hx.2.le⟩
        obtain ⟨b1, b2⟩ := hb x hx'
        rw [ceq (by linarith) b2]
        have := hqge x hx'
        linarith)
  have := hpm2 ⟨le_rfl, hσ⟩ hσI hσ
  dsimp only at this
  rw [hp0] at this
  norm_num at this
  linarith

/-- Along a receding-wall trajectory with 0 ≤ q < 2 before τ and p non-decreasing on [0, τ], p ≥ 0 from s = 1/20
on (`early`). -/
theorem late {K : ℝ} (hK : 0 < K) {f p q : ℝ → ℝ}
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (cl 2 (p η)) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (cl 2 (q η)) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q
      (-(K * cl (max η 0 + 2) (f η) * cl 2 (q η)) + 1 - cl 2 (p η) ^ 2) (Ici 0) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = -(1 / 1000)) (hq0 : q 0 = 0) {τ : ℝ}
    (good : ∀ s ∈ Ico 0 τ, 0 ≤ q s ∧ q s < 2) (hpm : MonotoneOn p (Icc 0 τ)) :
    ∀ s ∈ Icc 0 τ, 1 / 20 ≤ s → 0 ≤ p s := by
  intro s hs h20
  have h21 : (1 / 21 : ℝ) < τ := by linarith [hs.2]
  have e := early hK hf hp hq hf0 hp0 hq0 (hpm.mono (Icc_subset_Icc le_rfl h21.le))
    (fun x hx => ⟨(good x ⟨hx.1, lt_of_le_of_lt hx.2 h21⟩).1, (good x ⟨hx.1, lt_of_le_of_lt hx.2 h21⟩).2.le⟩)
  exact e.trans (hpm ⟨by norm_num, h21.le⟩ hs (by linarith))

set_option maxHeartbeats 1000000 in
theorem unclampS {K : ℝ} (hK5 : 5 ≤ K) (hK6 : K ≤ 6) {f p q : ℝ → ℝ}
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (cl 2 (p η)) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (cl 2 (q η)) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q
      (-(K * cl (max η 0 + 2) (f η) * cl 2 (q η)) + 1 - cl 2 (p η) ^ 2) (Ici 0) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = -(1 / 1000)) (hq0 : q 0 = 0)
    {η₀ : ℝ} (hη₀ : 0 < η₀) (hpre : ∀ s ∈ Icc 0 η₀, p s < 1)
    (hs1 : 0 ≤ p η₀) (hs2 : q η₀ < 3 * (1 - p η₀)) (hs3 : 11 / 15 < f η₀) :
    ∀ t ∈ Ici (0 : ℝ), (-(1 / 1000) ≤ p t ∧ (1 / 20 ≤ t → 0 ≤ p t)) ∧ p t < 1 ∧ 0 ≤ q t ∧ (0 < t → 0 < q t) ∧ q t < 2 ∧
      cS ≤ f t ∧ f t ≤ t ∧ (η₀ ≤ t → q t < 3 * (1 - p t) ∧ 11 / 15 < f t) := by
  have h00 : (0 : ℝ) ≤ 0 := le_rfl
  have hcS0 := cS_nonneg
  have hcS2 := cS_le
  have hcSn := cS_neg
  have hK0 : 0 < K := by linarith
  obtain ⟨δ, hδ, hstart⟩ := start hq hf0 hp0 hq0
  set δ₂ := δ / 2 with hδ₂
  have hδ₂0 : 0 < δ₂ := by rw [hδ₂]; linarith
  -- consequences of "no bad point on [0, τ)" on [0, τ]
  have conseq : ∀ τ, 0 ≤ τ → (∀ s ∈ Ico 0 τ, p s < 1 ∧ 0 ≤ q s ∧ q s < 2) →
      (∀ s ∈ Icc 0 τ, -(1 / 1000) ≤ p s ∧ p s ≤ 1 ∧ 0 ≤ q s ∧ q s ≤ 2 ∧ cS ≤ f s ∧ f s ≤ s) := by
    intro τ hτ good
    have hpm : MonotoneOn p (Icc 0 τ) := mono hp h00 (fun x hx => by
      have := good x ⟨hx.1.le, hx.2⟩
      rw [Checked.FSSep.SUnclamp.cl_eq (by linarith) this.2.2.le]; exact this.2.1)
    have hpge : ∀ s ∈ Icc 0 τ, -(1 / 1000) ≤ p s := fun s hs => by
      have := hpm ⟨le_rfl, hτ⟩ hs hs.1; rwa [hp0] at this
    have hpl := late hK0 hf hp hq hf0 hp0 hq0 (fun s hs => ⟨(good s hs).2.1, (good s hs).2.2⟩) hpm
    have hfd : MonotoneOn (fun s => f s + 1 / 1000 * s) (Icc 0 τ) :=
      mono (g' := fun s => cl 2 (p s) + 1 / 1000 * 1)
        (fun η hη => (hf η hη).add ((hasDerivWithinAt_id η (Ici 0)).const_mul (1 / 1000))) h00
        (fun x hx => by
          have := hpge x ⟨hx.1.le, hx.2.le⟩
          have h1 := (good x ⟨by linarith [hx.1], hx.2⟩).1
          rw [Checked.FSSep.SUnclamp.cl_eq (by linarith) (by linarith)]; linarith)
    have hfm : MonotoneOn f (Icc (1 / 20) τ) := mono hf (by norm_num) (fun x hx => by
      have := hpl x ⟨by linarith [hx.1], hx.2.le⟩ hx.1.le
      have h1 := (good x ⟨by linarith [hx.1], hx.2⟩).1
      rw [Checked.FSSep.SUnclamp.cl_eq (by linarith) (by linarith)]; exact this)
    have hgm : MonotoneOn (fun s => s - f s) (Icc 0 τ) :=
      mono (g' := fun s => 1 - cl 2 (p s))
        (fun η hη => ((hasDerivWithinAt_id η (Ici 0)).sub (hf η hη))) h00 (fun x hx => by
          have g := good x ⟨hx.1.le, hx.2⟩
          have := hpge x ⟨hx.1.le, hx.2.le⟩
          rw [Checked.FSSep.SUnclamp.cl_eq (by linarith) (by linarith)]; linarith [g.1])
    intro s hs
    have hps := hpge s hs
    have hfs : cS ≤ f s := by
      have hcSe : cS = -(1 / 1000) := rfl
      rcases le_total s (1 / 20) with h | h
      · have := hfd ⟨le_rfl, hτ⟩ hs hs.1
        dsimp only at this; rw [hf0] at this; linarith
      · have h1 := hfd ⟨le_rfl, hτ⟩ ⟨by norm_num, h.trans hs.2⟩ (by norm_num)
        have h2 := hfm ⟨le_rfl, h.trans hs.2⟩ ⟨h, hs.2⟩ h
        dsimp only at h1; rw [hf0] at h1; linarith
    have hfs2 : f s ≤ s := by
      have := hgm ⟨le_rfl, hτ⟩ hs hs.1; simp only [hf0] at this; linarith
    rcases eq_or_lt_of_le hs.2 with he | hlt
    · rcases eq_or_lt_of_le hs.1 with h0 | hpos
      · subst h0; rw [hp0, hq0]; exact ⟨by norm_num, by norm_num, le_rfl, by norm_num, hfs, hfs2⟩
      · subst he
        have hpc : ContinuousAt p s := (at_of hp hpos).continuousAt
        have hqc : ContinuousAt q s := (at_of hq hpos).continuousAt
        refine ⟨hps, Checked.FSNeg.NSlowInv.le_of_left hpos hpc (fun x hx => (good x ⟨hx.1.le, hx.2⟩).1.le),
          Checked.FSNeg.NSlowInv.ge_of_left hpos hqc (fun x hx => (good x ⟨hx.1.le, hx.2⟩).2.1),
          Checked.FSNeg.NSlowInv.le_of_left hpos hqc (fun x hx => (good x ⟨hx.1.le, hx.2⟩).2.2.le), hfs, hfs2⟩
    · have g := good s ⟨hs.1, hlt⟩
      exact ⟨hps, g.1.le, g.2.1, g.2.2.le, hfs, hfs2⟩
  have main : ∀ T, 0 ≤ T → ∀ s ∈ Icc 0 T, p s < 1 ∧ (0 < s → 0 < q s) ∧ q s < 2 ∧
      (η₀ ≤ s → q s < 3 * (1 - p s) ∧ 11 / 15 < f s) := by
    intro T hT
    by_contra hcon
    push Not at hcon
    set S : Set ℝ := Icc 0 T ∩ {s | 1 ≤ p s ∨ (δ₂ ≤ s ∧ q s ≤ 0) ∨ 2 ≤ q s ∨
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
      have : S = (Icc 0 T ∩ p ⁻¹' Ici 1) ∪ (Ici δ₂ ∩ (Icc 0 T ∩ q ⁻¹' Iic 0)) ∪ (Icc 0 T ∩ q ⁻¹' Ici 2) ∪
          (Ici η₀ ∩ ((Icc 0 T ∩ (fun s => q s - 3 * (1 - p s)) ⁻¹' Ici 0) ∪
            (Icc 0 T ∩ f ⁻¹' Iic (11 / 15)))) := by
        ext s
        simp only [hSdef, mem_inter_iff, mem_ofPred_eq, mem_union, mem_preimage, mem_Ici, mem_Iic,
          sub_nonneg]
        tauto
      rw [this]
      exact ((e1.union (isClosed_Ici.inter e2)).union e2').union (isClosed_Ici.inter (e3.union e4))
    obtain ⟨s₀, hs₀, hbad⟩ := hcon
    have hne : S.Nonempty := by
      refine ⟨s₀, hs₀, ?_⟩
      simp only [mem_ofPred_eq]
      by_contra hn
      push Not at hn
      obtain ⟨a1, a2, a3, a4⟩ := hn
      have hq' : 0 < s₀ → 0 < q s₀ := fun hs => by
        rcases lt_or_ge s₀ δ₂ with h | h
        · exact hstart s₀ ⟨hs, by linarith⟩
        · exact a2 h
      exact absurd (hbad a1 hq' a3) (by
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
      rcases this with h | ⟨h, _⟩ | h | ⟨h, _⟩ <;> linarith
    have hτpos : 0 < τ := lt_of_le_of_ne hτ0 (Ne.symm hτne)
    have good : ∀ s ∈ Ico 0 τ, p s < 1 ∧ (0 < s → 0 < q s) ∧ q s < 2 ∧
        (η₀ ≤ s → q s < 3 * (1 - p s) ∧ 11 / 15 < f s) := by
      intro s hs
      have hsS : s ∉ S := notMem_of_lt_csInf hs.2 hbdd
      have hsI : s ∈ Icc 0 T := ⟨hs.1, hs.2.le.trans hτS.1.2⟩
      have : ¬ (1 ≤ p s ∨ (δ₂ ≤ s ∧ q s ≤ 0) ∨ 2 ≤ q s ∨
          (η₀ ≤ s ∧ (3 * (1 - p s) ≤ q s ∨ f s ≤ 11 / 15))) := fun h => hsS ⟨hsI, h⟩
      push Not at this
      refine ⟨this.1, fun hs0 => ?_, this.2.2.1, fun h => this.2.2.2 h⟩
      rcases lt_or_ge s δ₂ with h | h
      · exact hstart s ⟨hs0, by linarith⟩
      · exact this.2.1 h
    have qnn : ∀ s ∈ Ico 0 τ, 0 ≤ q s := fun s hs => by
      rcases eq_or_lt_of_le hs.1 with h | h
      · rw [← h, hq0]
      · exact ((good s hs).2.1 h).le
    have C := conseq τ hτ0 (fun s hs => ⟨(good s hs).1, qnn s hs, (good s hs).2.2.1⟩)
    -- true derivatives on [0, τ]
    have tq : ∀ s ∈ Icc 0 τ, -(K * cl (max s 0 + 2) (f s) * cl 2 (q s)) + 1 - cl 2 (p s) ^ 2
        = -(K * f s * q s) + 1 - p s ^ 2 := by
      intro s hs
      obtain ⟨c1, c2, c3, c4, c5, c6⟩ := C s hs
      rw [Checked.FSSep.SUnclamp.cl_eq (c := max s 0 + 2) (y := f s) (by rw [max_eq_left hs.1]; linarith)
          (by rw [max_eq_left hs.1]; linarith),
        Checked.FSSep.SUnclamp.cl_eq (c := 2) (y := q s) (by linarith) c4, Checked.FSSep.SUnclamp.cl_eq (c := 2) (y := p s) (by linarith) (by linarith)]
    have tp : ∀ s ∈ Icc 0 τ, cl 2 (q s) = q s := fun s hs => by
      obtain ⟨c1, c2, c3, c4, c5, c6⟩ := C s hs; exact Checked.FSSep.SUnclamp.cl_eq (by linarith) c4
    have tf : ∀ s ∈ Icc 0 τ, cl 2 (p s) = p s := fun s hs => by
      obtain ⟨c1, c2, c3, c4, c5, c6⟩ := C s hs; exact Checked.FSSep.SUnclamp.cl_eq (by linarith) (by linarith)
    have hτI : τ ∈ Icc 0 τ := ⟨hτ0, le_rfl⟩
    obtain ⟨Cp0, Cp1, Cq0, Cq2, Cf0, Cft⟩ := C τ hτI
    have hqA : HasDerivAt q (-(K * f τ * q τ) + 1 - p τ ^ 2) τ := by
      have := at_of hq hτpos; rwa [tq τ hτI] at this
    have hpA : HasDerivAt p (q τ) τ := by
      have := at_of hp hτpos; rwa [tp τ hτI] at this
    -- energy: q τ < 2
    have hH : AntitoneOn (fun s => q s ^ 2 / 2 + p s ^ 3 / 3 - p s - 2 * K / 1000 * p s) (Icc 0 τ) :=
      anti (g' := fun s => q s * (-(K * cl (max s 0 + 2) (f s) * cl 2 (q s)) + 1 - cl 2 (p s) ^ 2)
          + (p s ^ 2 - 1) * cl 2 (q s) - 2 * K / 1000 * cl 2 (q s))
        (fun η hη => by
          have h1 := ((hq η hη).pow 2).div_const 2
          have h2 := ((hp η hη).pow 3).div_const 3
          have := ((h1.add h2).sub (hp η hη)).sub ((hp η hη).const_mul (2 * K / 1000))
          exact this.congr_deriv (by push_cast; ring))
        h00 (fun x hx => by
          have hx' : x ∈ Icc 0 τ := ⟨hx.1.le, hx.2.le⟩
          rw [tq x hx', tp x hx']
          obtain ⟨c1, c2, c3, c4, c5, c6⟩ := C x hx'
          have hf' : 0 ≤ f x + 1 / 1000 := by linarith [cS_nonneg]
          have e1 : 0 ≤ K * q x ^ 2 * (f x + 1 / 1000) := mul_nonneg (mul_nonneg hK0.le (sq_nonneg _)) hf'
          have e2 : 0 ≤ K * q x * (2 - q x) := mul_nonneg (mul_nonneg hK0.le c3) (by linarith)
          nlinarith)
    have hq2 : q τ < 2 := by
      have := hH ⟨le_rfl, hτ0⟩ hτI hτ0
      simp only [hp0, hq0] at this
      have hp3 : p τ - p τ ^ 3 / 3 ≤ 2 / 3 := by
        nlinarith [mul_nonneg (sq_nonneg (p τ - 1)) (show (0 : ℝ) ≤ p τ + 2 by linarith)]
      have hKp : 2 * K / 1000 * p τ ≤ 12 / 1000 := by nlinarith
      nlinarith
    -- p τ < 1
    have hp1 : p τ < 1 := by
      rcases le_or_gt τ η₀ with hle | hgt
      · exact hpre τ ⟨hτ0, hle⟩
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
          mul_pos (by linarith [hpre η₀ ⟨hη₀.le, le_rfl⟩]) (Real.exp_pos _)
        have hB := lt_of_lt_of_le hA this
        have := pos_of_mul_pos_left hB (Real.exp_pos _).le
        linarith
    -- q τ > 0: a zero of q with 0 ≤ p < 1 has q′ = 1 − p² > 0
    have hq0' : 0 < q τ := by
      rcases lt_or_eq_of_le Cq0 with h | h
      · exact h
      · exfalso
        have hd : 0 < -(K * f τ * q τ) + 1 - p τ ^ 2 := by rw [← h]; nlinarith
        exact Checked.FSNeg.NSlowInv.no_touch_from_above hτpos hqA hd h.symm
          (fun s hs => (good s ⟨hs.1.le, hs.2⟩).2.1 hs.1)
    have hlate : η₀ ≤ τ → q τ < 3 * (1 - p τ) ∧ 11 / 15 < f τ := by
      intro hle
      have hpmτ : MonotoneOn p (Icc 0 τ) := mono hp h00 (fun x hx => by
        have hx' : x ∈ Icc 0 τ := ⟨hx.1.le, hx.2.le⟩
        rw [tp x hx']; exact (C x hx').2.2.1)
      have hpl := late hK0 hf hp hq hf0 hp0 hq0 (fun s hs => ⟨qnn s hs, (good s hs).2.2.1⟩) hpmτ
      have hη20 : 1 / 20 ≤ η₀ := by have := (C η₀ ⟨hη₀.le, hle⟩).2.2.2.2.2; linarith
      have hfm : MonotoneOn f (Icc η₀ τ) := mono hf hη₀.le (fun x hx => by
        have hx' : x ∈ Icc 0 τ := ⟨hη₀.le.trans hx.1.le, hx.2.le⟩
        rw [tf x hx']; exact hpl x hx' (by linarith [hx.1]))
      have hfτ : 11 / 15 < f τ := lt_of_lt_of_le hs3 (hfm ⟨le_rfl, hle⟩ ⟨hle, le_rfl⟩ hle)
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
            have hm := mul_pos hK0 (show 0 < f τ - 11 / 15 by linarith)
            have e : 3 * K * f τ - 11 = 3 * (K * (f τ - 11 / 15)) + 11 / 5 * (K - 5) := by ring
            have hKf : 11 < 3 * K * f τ := by linarith
            have h3 : 11 - 3 * K * f τ - (1 - p τ) < 0 := by linarith
            have h4 : 0 < 1 - p τ := by linarith
            have := mul_neg_of_pos_of_neg h4 h3
            linarith
          exact Checked.FSNeg.NSlowInv.no_touch_from_above (g := fun s => -(q s - 3 * (1 - p s))) hgt
            hWA.neg hd (by linarith)
            (fun s hs => by
              have := ((good s ⟨hη₀.le.trans hs.1.le, hs.2⟩).2.2.2 hs.1.le).1; linarith)
    rcases hτS.2 with h | ⟨_, h⟩ | h | ⟨h1, h | h⟩
    · linarith
    · linarith
    · linarith
    · linarith [(hlate h1).1]
    · linarith [(hlate h1).2]
  intro t ht
  have ht0 : (0 : ℝ) ≤ t := ht
  have M := main t ht0
  have qg : ∀ s ∈ Ico 0 t, 0 ≤ q s ∧ q s < 2 := fun s hs => by
    have := M s ⟨hs.1, hs.2.le⟩
    refine ⟨?_, this.2.2.1⟩
    rcases eq_or_lt_of_le hs.1 with h | h
    · rw [← h, hq0]
    · exact (this.2.1 h).le
  have Call := conseq t ht0 (fun s hs => ⟨(M s ⟨hs.1, hs.2.le⟩).1, qg s hs⟩)
  have C := Call t ⟨ht0, le_rfl⟩
  have hpmt : MonotoneOn p (Icc 0 t) := mono hp h00 (fun x hx => by
    have c := Call x ⟨hx.1.le, hx.2.le⟩
    rw [Checked.FSSep.SUnclamp.cl_eq (by linarith [c.2.2.1]) c.2.2.2.1]; exact c.2.2.1)
  have Mt := M t ⟨ht0, le_rfl⟩
  exact ⟨⟨C.1, late hK0 hf hp hq hf0 hp0 hq0 qg hpmt t ⟨ht0, le_rfl⟩⟩, Mt.1, C.2.2.1, Mt.2.1, Mt.2.2.1,
    C.2.2.2.2.1, C.2.2.2.2.2, Mt.2.2.2⟩

/-- A zero-wall-shear trajectory of the clamped coefficient-K field with p ≤ 1 on [0, ∞) and no
touch (p = 1 and q = 0 together at some τ > 0) never meets a clamp: 0 ≤ p ≤ 1, 0 ≤ q < 2 with
q > 0 after 0, 0 ≤ f ≤ t. -/
theorem unclampS_neither {K : ℝ} (hK : 0 < K) (hK6 : K ≤ 6) {f p q : ℝ → ℝ}
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (cl 2 (p η)) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (cl 2 (q η)) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q
      (-(K * cl (max η 0 + 2) (f η) * cl 2 (q η)) + 1 - cl 2 (p η) ^ 2) (Ici 0) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = -(1 / 1000)) (hq0 : q 0 = 0)
    (hp1 : ∀ t ∈ Ici (0 : ℝ), p t ≤ 1)
    (htouch : ∀ τ, 0 < τ → p τ = 1 → q τ = 0 → False) :
    ∀ t ∈ Ici (0 : ℝ), (-(1 / 1000) ≤ p t ∧ (1 / 20 ≤ t → 0 ≤ p t)) ∧ p t ≤ 1 ∧ 0 ≤ q t ∧ (0 < t → 0 < q t) ∧ q t < 2 ∧
      cS ≤ f t ∧ f t ≤ t := by
  have h00 : (0 : ℝ) ≤ 0 := le_rfl
  have hcS0 := cS_nonneg
  have hcS2 := cS_le
  have hcSn := cS_neg
  obtain ⟨δ, hδ, hstart⟩ := start hq hf0 hp0 hq0
  set δ₂ := δ / 2 with hδ₂
  have hδ₂0 : 0 < δ₂ := by rw [hδ₂]; linarith
  have conseq : ∀ τ, 0 ≤ τ → (∀ s ∈ Ico 0 τ, 0 ≤ q s ∧ q s < 2) →
      (∀ s ∈ Icc 0 τ, -(1 / 1000) ≤ p s ∧ p s ≤ 1 ∧ 0 ≤ q s ∧ q s ≤ 2 ∧ cS ≤ f s ∧ f s ≤ s) := by
    intro τ hτ good
    have hpm : MonotoneOn p (Icc 0 τ) := mono hp h00 (fun x hx => by
      have := good x ⟨hx.1.le, hx.2⟩
      rw [Checked.FSSep.SUnclamp.cl_eq (by linarith) this.2.le]; exact this.1)
    have hpge : ∀ s ∈ Icc 0 τ, -(1 / 1000) ≤ p s := fun s hs => by
      have := hpm ⟨le_rfl, hτ⟩ hs hs.1; rwa [hp0] at this
    have hpl := late hK hf hp hq hf0 hp0 hq0 (fun s hs => good s hs) hpm
    have hfd : MonotoneOn (fun s => f s + 1 / 1000 * s) (Icc 0 τ) :=
      mono (g' := fun s => cl 2 (p s) + 1 / 1000 * 1)
        (fun η hη => (hf η hη).add ((hasDerivWithinAt_id η (Ici 0)).const_mul (1 / 1000))) h00
        (fun x hx => by
          have := hpge x ⟨hx.1.le, hx.2.le⟩
          have h1 := hp1 x (show (0 : ℝ) ≤ x by linarith [hx.1])
          rw [Checked.FSSep.SUnclamp.cl_eq (by linarith) (by linarith)]; linarith)
    have hfm : MonotoneOn f (Icc (1 / 20) τ) := mono hf (by norm_num) (fun x hx => by
      have := hpl x ⟨by linarith [hx.1], hx.2.le⟩ hx.1.le
      have h1 := hp1 x (show (0 : ℝ) ≤ x by linarith [hx.1])
      rw [Checked.FSSep.SUnclamp.cl_eq (by linarith) (by linarith)]; exact this)
    have hgm : MonotoneOn (fun s => s - f s) (Icc 0 τ) :=
      mono (g' := fun s => 1 - cl 2 (p s))
        (fun η hη => ((hasDerivWithinAt_id η (Ici 0)).sub (hf η hη))) h00 (fun x hx => by
          have := hpge x ⟨hx.1.le, hx.2.le⟩
          have h1 := hp1 x hx.1.le
          rw [Checked.FSSep.SUnclamp.cl_eq (by linarith) (by linarith)]; linarith)
    intro s hs
    have hps := hpge s hs
    have hfs : cS ≤ f s := by
      have hcSe : cS = -(1 / 1000) := rfl
      rcases le_total s (1 / 20) with h | h
      · have := hfd ⟨le_rfl, hτ⟩ hs hs.1
        dsimp only at this; rw [hf0] at this; linarith
      · have h1 := hfd ⟨le_rfl, hτ⟩ ⟨by norm_num, h.trans hs.2⟩ (by norm_num)
        have h2 := hfm ⟨le_rfl, h.trans hs.2⟩ ⟨h, hs.2⟩ h
        dsimp only at h1; rw [hf0] at h1; linarith
    have hfs2 : f s ≤ s := by
      have := hgm ⟨le_rfl, hτ⟩ hs hs.1; simp only [hf0] at this; linarith
    have hp1s := hp1 s hs.1
    rcases eq_or_lt_of_le hs.2 with he | hlt
    · rcases eq_or_lt_of_le hs.1 with h0 | hpos
      · subst h0; rw [hq0]; exact ⟨hps, hp1s, le_rfl, by norm_num, hfs, hfs2⟩
      · subst he
        have hqc : ContinuousAt q s := (at_of hq hpos).continuousAt
        refine ⟨hps, hp1s,
          Checked.FSNeg.NSlowInv.ge_of_left hpos hqc (fun x hx => (good x ⟨hx.1.le, hx.2⟩).1),
          Checked.FSNeg.NSlowInv.le_of_left hpos hqc (fun x hx => (good x ⟨hx.1.le, hx.2⟩).2.le),
          hfs, hfs2⟩
    · have g := good s ⟨hs.1, hlt⟩
      exact ⟨hps, hp1s, g.1, g.2.le, hfs, hfs2⟩
  have main : ∀ T, 0 ≤ T → ∀ s ∈ Icc 0 T, (0 < s → 0 < q s) ∧ q s < 2 := by
    intro T hT
    by_contra hcon
    push Not at hcon
    set S : Set ℝ := Icc 0 T ∩ {s | (δ₂ ≤ s ∧ q s ≤ 0) ∨ 2 ≤ q s} with hSdef
    have hqc := cont_of hq (b := T) h00
    have hSc : IsClosed S := by
      have e2 : IsClosed (Icc 0 T ∩ q ⁻¹' Iic 0) := hqc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
      have e2' : IsClosed (Icc 0 T ∩ q ⁻¹' Ici 2) := hqc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
      have : S = (Ici δ₂ ∩ (Icc 0 T ∩ q ⁻¹' Iic 0)) ∪ (Icc 0 T ∩ q ⁻¹' Ici 2) := by
        ext s
        simp only [hSdef, mem_inter_iff, mem_ofPred_eq, mem_union, mem_preimage, mem_Ici, mem_Iic]
        tauto
      rw [this]; exact (isClosed_Ici.inter e2).union e2'
    obtain ⟨s₀, hs₀, hbad⟩ := hcon
    have hne : S.Nonempty := by
      refine ⟨s₀, hs₀, ?_⟩
      simp only [mem_ofPred_eq]
      by_contra hn
      push Not at hn
      have hq' : 0 < s₀ → 0 < q s₀ := fun hs => by
        rcases lt_or_ge s₀ δ₂ with h | h
        · exact hstart s₀ ⟨hs, by linarith⟩
        · exact hn.1 h
      exact absurd (hbad hq') (not_le.2 hn.2)
    have hbdd : BddBelow S := ⟨0, fun s hs => hs.1.1⟩
    set τ := sInf S with hτ
    have hτS : τ ∈ S := hSc.csInf_mem hne hbdd
    have hτ0 : 0 ≤ τ := hτS.1.1
    have hτne : τ ≠ 0 := by
      intro he
      have := hτS.2
      rw [he] at this
      simp only [mem_ofPred_eq, hq0] at this
      rcases this with ⟨h, _⟩ | h <;> linarith
    have hτpos : 0 < τ := lt_of_le_of_ne hτ0 (Ne.symm hτne)
    have good : ∀ s ∈ Ico 0 τ, (0 < s → 0 < q s) ∧ q s < 2 := by
      intro s hs
      have hsS : s ∉ S := notMem_of_lt_csInf hs.2 hbdd
      have hsI : s ∈ Icc 0 T := ⟨hs.1, hs.2.le.trans hτS.1.2⟩
      have : ¬ ((δ₂ ≤ s ∧ q s ≤ 0) ∨ 2 ≤ q s) := fun h => hsS ⟨hsI, h⟩
      push Not at this
      refine ⟨fun hs0 => ?_, this.2⟩
      rcases lt_or_ge s δ₂ with h | h
      · exact hstart s ⟨hs0, by linarith⟩
      · exact this.1 h
    have qnn : ∀ s ∈ Ico 0 τ, 0 ≤ q s := fun s hs => by
      rcases eq_or_lt_of_le hs.1 with h | h
      · rw [← h, hq0]
      · exact ((good s hs).1 h).le
    have C := conseq τ hτ0 (fun s hs => ⟨qnn s hs, (good s hs).2⟩)
    have tq : ∀ s ∈ Icc 0 τ, -(K * cl (max s 0 + 2) (f s) * cl 2 (q s)) + 1 - cl 2 (p s) ^ 2
        = -(K * f s * q s) + 1 - p s ^ 2 := by
      intro s hs
      obtain ⟨c1, c2, c3, c4, c5, c6⟩ := C s hs
      rw [Checked.FSSep.SUnclamp.cl_eq (c := max s 0 + 2) (y := f s) (by rw [max_eq_left hs.1]; linarith)
          (by rw [max_eq_left hs.1]; linarith),
        Checked.FSSep.SUnclamp.cl_eq (c := 2) (y := q s) (by linarith) c4, Checked.FSSep.SUnclamp.cl_eq (c := 2) (y := p s) (by linarith) (by linarith)]
    have tp : ∀ s ∈ Icc 0 τ, cl 2 (q s) = q s := fun s hs => by
      obtain ⟨c1, c2, c3, c4, c5, c6⟩ := C s hs; exact Checked.FSSep.SUnclamp.cl_eq (by linarith) c4
    have hτI : τ ∈ Icc 0 τ := ⟨hτ0, le_rfl⟩
    obtain ⟨Cp0, Cp1, Cq0, Cq2, Cf0, Cft⟩ := C τ hτI
    have hqA : HasDerivAt q (-(K * f τ * q τ) + 1 - p τ ^ 2) τ := by
      have := at_of hq hτpos; rwa [tq τ hτI] at this
    have hH : AntitoneOn (fun s => q s ^ 2 / 2 + p s ^ 3 / 3 - p s - 2 * K / 1000 * p s) (Icc 0 τ) :=
      anti (g' := fun s => q s * (-(K * cl (max s 0 + 2) (f s) * cl 2 (q s)) + 1 - cl 2 (p s) ^ 2)
          + (p s ^ 2 - 1) * cl 2 (q s) - 2 * K / 1000 * cl 2 (q s))
        (fun η hη => by
          have h1 := ((hq η hη).pow 2).div_const 2
          have h2 := ((hp η hη).pow 3).div_const 3
          have := ((h1.add h2).sub (hp η hη)).sub ((hp η hη).const_mul (2 * K / 1000))
          exact this.congr_deriv (by push_cast; ring))
        h00 (fun x hx => by
          have hx' : x ∈ Icc 0 τ := ⟨hx.1.le, hx.2.le⟩
          rw [tq x hx', tp x hx']
          obtain ⟨c1, c2, c3, c4, c5, c6⟩ := C x hx'
          have hf' : 0 ≤ f x + 1 / 1000 := by linarith [cS_nonneg]
          have e1 : 0 ≤ K * q x ^ 2 * (f x + 1 / 1000) := mul_nonneg (mul_nonneg hK.le (sq_nonneg _)) hf'
          have e2 : 0 ≤ K * q x * (2 - q x) := mul_nonneg (mul_nonneg hK.le c3) (by linarith)
          nlinarith)
    have hq2 : q τ < 2 := by
      have := hH ⟨le_rfl, hτ0⟩ hτI hτ0
      simp only [hp0, hq0] at this
      have hp3 : p τ - p τ ^ 3 / 3 ≤ 2 / 3 := by
        nlinarith [mul_nonneg (sq_nonneg (p τ - 1)) (show (0 : ℝ) ≤ p τ + 2 by linarith)]
      have hKp : 2 * K / 1000 * p τ ≤ 12 / 1000 := by nlinarith
      nlinarith
    have hq0' : 0 < q τ := by
      rcases lt_or_eq_of_le Cq0 with h | h
      · exact h
      · exfalso
        rcases lt_or_eq_of_le Cp1 with hp | hp
        · have hd : 0 < -(K * f τ * q τ) + 1 - p τ ^ 2 := by rw [← h]; nlinarith
          exact Checked.FSNeg.NSlowInv.no_touch_from_above hτpos hqA hd h.symm
            (fun s hs => (good s ⟨hs.1.le, hs.2⟩).1 hs.1)
        · exact htouch τ hτpos hp h.symm
    rcases hτS.2 with ⟨_, h⟩ | h <;> linarith
  intro t ht
  have ht0 : (0 : ℝ) ≤ t := ht
  have M := main t ht0
  have qg : ∀ s ∈ Ico 0 t, 0 ≤ q s ∧ q s < 2 := fun s hs => by
    have := M s ⟨hs.1, hs.2.le⟩
    refine ⟨?_, this.2⟩
    rcases eq_or_lt_of_le hs.1 with h | h
    · rw [← h, hq0]
    · exact (this.1 h).le
  have Call := conseq t ht0 qg
  have C := Call t ⟨ht0, le_rfl⟩
  have hpmt : MonotoneOn p (Icc 0 t) := mono hp h00 (fun x hx => by
    have c := Call x ⟨hx.1.le, hx.2.le⟩
    rw [Checked.FSSep.SUnclamp.cl_eq (by linarith [c.2.2.1]) c.2.2.2.1]; exact c.2.2.1)
  have Mt := M t ⟨ht0, le_rfl⟩
  exact ⟨⟨C.1, late hK hf hp hq hf0 hp0 hq0 qg hpmt t ⟨ht0, le_rfl⟩⟩, C.2.1, C.2.2.1, Mt.1, Mt.2,
    C.2.2.2.2.1, C.2.2.2.2.2⟩



theorem comps (K : ℝ) :
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt (fun t => (flowK K t).1) (cl 2 (flowK K η).2.1) (Ici 0) η) ∧
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt (fun t => (flowK K t).2.1) (cl 2 (flowK K η).2.2) (Ici 0) η) ∧
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt (fun t => (flowK K t).2.2)
      (-(K * cl (max η 0 + 2) (flowK K η).1 * cl 2 (flowK K η).2.2) + 1 - cl 2 (flowK K η).2.1 ^ 2)
      (Ici 0) η) := by
  refine ⟨fun η hη => ?_, fun η hη => ?_, fun η hη => ?_⟩
  · exact (hasFDerivAt_fst.comp_hasDerivWithinAt η (flowK_deriv K η hη))
  · exact (hasFDerivAt_fst.comp_hasDerivWithinAt η
      (hasFDerivAt_snd.comp_hasDerivWithinAt η (flowK_deriv K η hη)))
  · exact (hasFDerivAt_snd.comp_hasDerivWithinAt η
      (hasFDerivAt_snd.comp_hasDerivWithinAt η (flowK_deriv K η hη)))

theorem dist_c0 {a b : ℝ × ℝ × ℝ} : |a.1 - b.1| ≤ dist a b := by
  rw [← Real.dist_eq, Prod.dist_eq]; exact le_max_left _ _

theorem dist_c1 {a b : ℝ × ℝ × ℝ} : |a.2.1 - b.2.1| ≤ dist a b := by
  have h1 : dist a.2 b.2 ≤ dist a b := by rw [Prod.dist_eq]; exact le_max_right _ _
  have h2 : dist a.2.1 b.2.1 ≤ dist a.2 b.2 := by rw [Prod.dist_eq]; exact le_max_left _ _
  rw [← Real.dist_eq]; linarith

theorem dist_c2 {a b : ℝ × ℝ × ℝ} : |a.2.2 - b.2.2| ≤ dist a b := by
  have h1 : dist a.2 b.2 ≤ dist a b := by rw [Prod.dist_eq]; exact le_max_right _ _
  have h2 : dist a.2.2 b.2.2 ≤ dist a.2 b.2 := by rw [Prod.dist_eq]; exact le_max_right _ _
  rw [← Real.dist_eq]; linarith

theorem cont_comp (K : ℝ) (η : ℝ) : ContinuousOn (flowK K) (Icc 0 η) := fun s hs =>
  ((flowK_deriv K s hs.1).continuousWithinAt).mono (fun x hx => hx.1)

theorem over_open (K₀ : ℝ) (h : Over (flowK K₀)) :
    ∃ δ > 0, ∀ K, |K - K₀| < δ → Over (flowK K) := by
  obtain ⟨η, hη, hp⟩ := h
  obtain ⟨δ, hδ, hcl⟩ := flowK_cont η hη.le K₀ (show 0 < (flowK K₀ η).2.1 - 1 by linarith)
  refine ⟨δ, hδ, fun K hK => ⟨η, hη, ?_⟩⟩
  have k := (dist_c1 (a := flowK K η) (b := flowK K₀ η)).trans_lt (hcl K hK η ⟨hη.le, le_rfl⟩)
  rw [abs_lt] at k; linarith [k.1]

/-- Along a SlowS trajectory with K ≥ 5, every clamp is inactive (`SUnclamp.unclampS`). -/
theorem slow_unclamp {K : ℝ} (hK5 : 5 ≤ K) (hK6 : K ≤ 6) {η₀ : ℝ} (hη₀ : 0 < η₀)
    (hpre : ∀ s ∈ Icc 0 η₀, (flowK K s).2.1 < 1) (hs1 : 0 ≤ (flowK K η₀).2.1)
    (hs2 : (flowK K η₀).2.2 < 3 * (1 - (flowK K η₀).2.1)) (hs3 : 11 / 15 < (flowK K η₀).1) :
    ∀ t ∈ Ici (0 : ℝ), (-(1 / 1000) ≤ (flowK K t).2.1 ∧ (1 / 20 ≤ t → 0 ≤ (flowK K t).2.1)) ∧ (flowK K t).2.1 < 1 ∧
      0 ≤ (flowK K t).2.2 ∧
      (0 < t → 0 < (flowK K t).2.2) ∧ (flowK K t).2.2 < 2 ∧ cS ≤ (flowK K t).1 ∧ (flowK K t).1 ≤ t ∧
      (η₀ ≤ t → (flowK K t).2.2 < 3 * (1 - (flowK K t).2.1) ∧ 11 / 15 < (flowK K t).1) := by
  obtain ⟨hF, hP, hQ⟩ := comps K
  exact unclampS hK5 hK6 hF hP hQ (by simp [flowK_zero]) (by simp [flowK_zero])
    (by simp [flowK_zero]) hη₀ hpre hs1 hs2 hs3

theorem slowS_open (K₀ : ℝ) (hK₀ : 5 ≤ K₀) (hK₀6 : K₀ ≤ 6) (h : SlowS (flowK K₀)) :
    ∃ δ > 0, ∀ K, |K - K₀| < δ → SlowS (flowK K) := by
  obtain ⟨η, hη, hpre, h1, h2, h3⟩ := h
  have U := slow_unclamp hK₀ hK₀6 hη hpre h1 h2 h3
  -- p(η) > 0 strictly: p is strictly increasing on [0, η] since q > 0 on (0, η)
  have hpη : 0 < (flowK K₀ η).2.1 := by
    obtain ⟨_, hP, _⟩ := comps K₀
    have hη20 : 1 / 20 < η := by have u := U η hη.le; linarith [u.2.2.2.2.2.2.1]
    have hsm := Checked.FalknerSkan.LimitCore.smono hP (by norm_num : (0 : ℝ) ≤ 1 / 20) (b := η) (fun x hx => by
      have u := U x (show (0 : ℝ) ≤ x by linarith [hx.1])
      rw [Checked.FSSep.SUnclamp.cl_eq (by linarith [u.2.2.1]) (by linarith [u.2.2.2.2.1])]
      exact u.2.2.2.1 (by linarith [hx.1]))
    have := hsm ⟨le_rfl, hη20.le⟩ ⟨hη20.le, le_rfl⟩ hη20
    linarith [(U (1 / 20) (by norm_num)).1.2 le_rfl]
  have hcp : ContinuousOn (fun s => (flowK K₀ s).2.1) (Icc 0 η) :=
    (continuous_fst.comp continuous_snd).comp_continuousOn (cont_comp K₀ η)
  obtain ⟨s1, hs1, hmax⟩ := isCompact_Icc.exists_isMaxOn ⟨0, ⟨le_rfl, hη.le⟩⟩ hcp
  have hM : (flowK K₀ s1).2.1 < 1 := hpre s1 hs1
  set ε := min (min (1 - (flowK K₀ s1).2.1) (flowK K₀ η).2.1)
    (min ((3 * (1 - (flowK K₀ η).2.1) - (flowK K₀ η).2.2) / 4) ((flowK K₀ η).1 - 11 / 15)) with hε
  have e1 : ε ≤ 1 - (flowK K₀ s1).2.1 := (min_le_left _ _).trans (min_le_left _ _)
  have e2 : ε ≤ (flowK K₀ η).2.1 := (min_le_left _ _).trans (min_le_right _ _)
  have e3 : ε ≤ (3 * (1 - (flowK K₀ η).2.1) - (flowK K₀ η).2.2) / 4 :=
    (min_le_right _ _).trans (min_le_left _ _)
  have e4 : ε ≤ (flowK K₀ η).1 - 11 / 15 := (min_le_right _ _).trans (min_le_right _ _)
  have hε0 : 0 < ε := lt_min (lt_min (by linarith) hpη) (lt_min (by linarith) (by linarith))
  obtain ⟨δ, hδ, hcl⟩ := flowK_cont η hη.le K₀ hε0
  refine ⟨δ, hδ, fun K hK => ⟨η, hη, ?_, ?_, ?_, ?_⟩⟩
  · intro s hs
    have k1 := (dist_c1 (a := flowK K s) (b := flowK K₀ s)).trans_lt (hcl K hK s hs)
    have := hmax hs
    simp only [mem_setOf_eq] at this
    rw [abs_lt] at k1
    linarith
  · have k1 := (dist_c1 (a := flowK K η) (b := flowK K₀ η)).trans_lt (hcl K hK η ⟨hη.le, le_rfl⟩)
    rw [abs_lt] at k1; linarith
  · have k := hcl K hK η ⟨hη.le, le_rfl⟩
    have k1 := (dist_c1 (a := flowK K η) (b := flowK K₀ η)).trans_lt k
    have k2 := (dist_c2 (a := flowK K η) (b := flowK K₀ η)).trans_lt k
    rw [abs_lt] at k1 k2; linarith
  · have k0 := (dist_c0 (a := flowK K η) (b := flowK K₀ η)).trans_lt (hcl K hK η ⟨hη.le, le_rfl⟩)
    rw [abs_lt] at k0; linarith

theorem slowS_not_over {K : ℝ} (hK5 : 5 ≤ K) (hK6 : K ≤ 6) (hS : SlowS (flowK K)) (hO : Over (flowK K)) :
    False := by
  obtain ⟨η₀, hη₀, hpre, hs1, hs2, hs3⟩ := hS
  have U := slow_unclamp hK5 hK6 hη₀ hpre hs1 hs2 hs3
  obtain ⟨η, hη, hp⟩ := hO
  have := (U η hη.le).2.1
  linarith

/-- Neither event: the flow solves the scaled problem with zero wall shear, in the decay class. -/
theorem neither_class {K : ℝ} (hK : 0 < K) (hK6 : K ≤ 6) (hnS : ¬ SlowS (flowK K)) (hnO : ¬ Over (flowK K)) :
    let F := fun t => (flowK K t).1
    let P := fun t => (flowK K t).2.1
    let Q := fun t => (flowK K t).2.2
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt F (P η) (Ici 0) η) ∧
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt P (Q η) (Ici 0) η) ∧
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt Q (-(K * F η * Q η) + 1 - P η ^ 2) (Ici 0) η) ∧
    Tendsto P atTop (𝓝 1) ∧ (∀ η ∈ Ioi (0 : ℝ), 0 < Q η) ∧
    (∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - P η) ≤ Q η) := by
  intro F P Q
  have hcS2 := cS_le
  have hcS0 := cS_nonneg
  obtain ⟨hF, hP, hQ⟩ := comps K
  have h0 := flowK_zero K
  have hF0 : F 0 = 0 := by simp [F, h0]
  have hP0 : P 0 = -(1 / 1000) := by simp [P, h0]
  have hQ0 : Q 0 = 0 := by simp [Q, h0]
  have hp1 : ∀ t ∈ Ici (0 : ℝ), P t ≤ 1 := by
    intro t ht
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ t from ht) with h | h
    · rw [← h, hP0]; norm_num
    · by_contra hc; push Not at hc; exact hnO ⟨t, h, hc⟩
  have htouch : ∀ τ, 0 < τ → P τ = 1 → Q τ = 0 → False := by
    intro τ hτ hpτ hqτ
    set Z : ℝ → ℝ × ℝ × ℝ := fun t => (F τ + (t - τ), 1, 0) with hZ
    have hZd : ∀ t ∈ Icc 0 τ, HasDerivWithinAt Z (vS K t (Z t)) (Icc 0 τ) t := by
      intro t _
      have hv : vS K t (Z t) = (1, 0, 0) := by
        simp only [hZ, vS]
        rw [Checked.FSSep.SUnclamp.cl_eq (c := 2) (y := 1) (by norm_num) (by norm_num),
          Checked.FSSep.SUnclamp.cl_eq (c := 2) (y := 0) (by norm_num) (by norm_num)]
        simp
      rw [hv]
      have a1 : HasDerivWithinAt (fun t => F τ + (t - τ)) 1 (Icc 0 τ) t :=
        ((hasDerivWithinAt_id t _).sub_const τ).const_add _ |>.congr_deriv (by simp)
      exact a1.prodMk ((hasDerivWithinAt_const t _ (1 : ℝ)).prodMk (hasDerivWithinAt_const t _ (0 : ℝ)))
    have hY : ∀ t ∈ Icc 0 τ, HasDerivWithinAt (flowK K) (vS K t (flowK K t)) (Icc 0 τ) t :=
      fun t ht => (flowK_deriv K t ht.1).mono (fun x hx => hx.1)
    have hZτ : flowK K τ = Z τ := by
      simp only [hZ, sub_self, add_zero]
      ext
      · rfl
      · exact hpτ
      · exact hqτ
    have := Checked.FSSep.SFlow.unique_left hτ.le hY hZd hZτ (⟨le_rfl, hτ.le⟩ : (0 : ℝ) ∈ Icc 0 τ)
    have h2 := congrArg (fun y => y.2.1) this
    simp only [hZ, h0] at h2
    norm_num at h2
  have U := unclampS_neither hK hK6 hF hP hQ hF0 hP0 hQ0 hp1 htouch
  have ceq := @Checked.FSSep.SUnclamp.cl_eq
  have tF : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt F (P η) (Ici 0) η := fun η hη => by
    have u := U η hη
    have := hF η hη; rwa [ceq (by linarith [u.1.1]) (by linarith [u.2.1])] at this
  have tP : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt P (Q η) (Ici 0) η := fun η hη => by
    have u := U η hη
    have := hP η hη; rwa [ceq (by linarith [u.2.2.1]) (by linarith [u.2.2.2.2.1])] at this
  have tQ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt Q (-(K * F η * Q η) + 1 - P η ^ 2) (Ici 0) η :=
    fun η hη => by
    have u := U η hη
    have hη0 : (0 : ℝ) ≤ η := hη
    have := hQ η hη
    rwa [ceq (c := max η 0 + 2) (y := F η) (by rw [max_eq_left hη0]; linarith [u.2.2.2.2.2.1])
        (by rw [max_eq_left hη0]; linarith [u.2.2.2.2.2.2]),
      ceq (c := 2) (y := Q η) (by linarith [u.2.2.1]) (by linarith [u.2.2.2.2.1]),
      ceq (c := 2) (y := P η) (by linarith [u.1.1]) (by linarith [u.2.1])] at this
  have hqpos : ∀ η ∈ Ioi (0 : ℝ), 0 < Q η := fun η hη => (U η (le_of_lt (show (0 : ℝ) < η from hη))).2.2.2.1 hη
  have hplt : ∀ η ∈ Ici (0 : ℝ), P η < 1 := by
    intro η hη
    have hη0 : (0 : ℝ) ≤ η := hη
    have hsm := Checked.FalknerSkan.LimitCore.smono tP hη0 (b := η + 1)
      (fun x hx => hqpos x (lt_of_le_of_lt hη0 hx.1))
    have := hsm ⟨le_rfl, by linarith⟩ ⟨by linarith, le_rfl⟩ (by linarith)
    linarith [hp1 (η + 1) (show (0 : ℝ) ≤ η + 1 by linarith)]
  have hlim : Tendsto P atTop (𝓝 1) :=
    Checked.FSNeg.NLimit.neg_limit hK tF tP tQ (a := 1) (by norm_num)
      (fun η hη => hqpos η (show (0 : ℝ) < η from lt_of_lt_of_le one_pos hη))
      (by linarith [(U 1 (by norm_num)).1.2 (by norm_num)]) (fun η hη => hplt η (show (0 : ℝ) ≤ η from le_trans zero_le_one hη))
  have hft := Checked.FSNeg.NLimit.f_tendsto tF hlim
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hft.eventually_gt_atTop (11 / 15))
  set a := max N 1 with ha
  have ha0 : (0 : ℝ) ≤ a := le_trans (by norm_num) (le_max_right _ _)
  have hlow : ∀ η ∈ Ici a, 3 * (1 - P η) ≤ Q η := by
    intro η hη
    have hη' : a ≤ η := hη
    by_contra hc
    push Not at hc
    apply hnS
    refine ⟨η, lt_of_lt_of_le (by norm_num) ((le_max_right N 1).trans hη'), fun s hs => ?_,
      (U η (ha0.trans hη')).1.2 (by linarith [(le_max_right N 1).trans hη']), hc, hN η ((le_max_left N 1).trans hη')⟩
    exact hplt s hs.1
  refine ⟨tF, tP, tQ, hlim, hqpos, ?_⟩
  exact Checked.FSNeg.NRiccati.riccati_up hK (by norm_num : (0 : ℝ) < 3)
    tP tQ ha0 (fun η hη => hplt η (ha0.trans hη)) hft hlow


theorem core_sepR {lo hi : ℝ} (hlo5 : 5 ≤ lo) (hlh : lo < hi) (hhi6 : hi ≤ 6) (hO : ChainKR lo Over) (hS : ChainKR hi SlowS) :
    ∃ β, -(1 / lo) < β ∧ β < -(1 / hi) ∧
    ∃ f p q : ℝ → ℝ,
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - β * (1 - p η ^ 2)) (Ici 0) η) ∧
      f 0 = 0 ∧ p 0 < 0 ∧ q 0 = 0 ∧ Tendsto p atTop (𝓝 1) ∧
      (∀ η ∈ Ioi (0 : ℝ), 0 < q η) ∧
      (∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - p η) ≤ q η) := by
  have over_lo : Over (flowK lo) := of_chain hO
  have slow_hi : SlowS (flowK hi) := of_chain hS
  set S : Set ℝ := {K | K ∈ Icc lo hi ∧ Over (flowK K)} with hSd
  have hloS : lo ∈ S := ⟨⟨le_rfl, hlh.le⟩, over_lo⟩
  have hne : S.Nonempty := ⟨lo, hloS⟩
  have hbdd : BddAbove S := ⟨hi, fun K hK => hK.1.2⟩
  set a := sSup S with ha
  have hloa := le_csSup hbdd hloS
  obtain ⟨δ2, hδ2, hS2⟩ := slowS_open hi (by linarith) hhi6 slow_hi
  have ha_lt : a < hi := by
    have hub : ∀ K ∈ S, K ≤ hi - δ2 / 2 := by
      intro K hK
      by_contra hc
      push Not at hc
      have hSK := hS2 K (by rw [abs_lt]; constructor <;> linarith [hK.1.2])
      exact slowS_not_over (by linarith [hK.1.1]) (by linarith [hK.1.2]) hSK hK.2
    have := csSup_le hne hub
    linarith
  have hnO : ¬ Over (flowK a) := by
    intro hOa
    obtain ⟨δ, hδ, hOa'⟩ := over_open a hOa
    obtain ⟨K', hK'd⟩ : ∃ x : ℝ, x = a + min (δ / 2) ((hi - a) / 2) := ⟨_, rfl⟩
    have h1 : 0 < min (δ / 2) ((hi - a) / 2) := lt_min (by linarith) (by linarith)
    have h2 : min (δ / 2) ((hi - a) / 2) ≤ δ / 2 := min_le_left _ _
    have h3 : min (δ / 2) ((hi - a) / 2) ≤ (hi - a) / 2 := min_le_right _ _
    have hK'S : K' ∈ S := ⟨⟨by linarith, by linarith⟩,
      hOa' K' (by rw [abs_lt]; constructor <;> linarith)⟩
    have := le_csSup hbdd hK'S
    linarith
  have hnS : ¬ SlowS (flowK a) := by
    intro hSa
    obtain ⟨δ, hδ, hSa'⟩ := slowS_open a (by linarith) (by linarith) hSa
    obtain ⟨K, hKS, hKa⟩ := exists_lt_of_lt_csSup hne (show a - δ < a by linarith)
    have hle : K ≤ a := le_csSup hbdd hKS
    exact slowS_not_over (by linarith [hKS.1.1]) (by linarith [hKS.1.2])
      (hSa' K (by rw [abs_lt]; constructor <;> linarith)) hKS.2
  have hlo_lt : lo < a := by
    rcases eq_or_lt_of_le hloa with h | h
    · exact absurd (by rw [ha, ← h]; exact over_lo) hnO
    · exact h
  have ha0 : 0 < a := by linarith
  obtain ⟨tF, tP, tQ, hlim, hqpos, hdec⟩ := neither_class ha0 (by linarith) hnS hnO
  set F := fun t => (flowK a t).1
  set P := fun t => (flowK a t).2.1
  set Q := fun t => (flowK a t).2.2
  have hF0 : F 0 = 0 := by simp [F, flowK_zero]
  have hP0 : P 0 = -(1 / 1000) := by simp [P, flowK_zero]
  have hQ0 : Q 0 = 0 := by simp [Q, flowK_zero]
  have hc : 0 < Real.sqrt a := Real.sqrt_pos.2 ha0
  have hc2 : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha0.le
  have tQ' : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt Q (-(a * F η * Q η) - (-1) * (1 - P η ^ 2)) (Ici 0) η :=
    fun η hη => (tQ η hη).congr_deriv (by ring)
  obtain ⟨A, B, C⟩ := Checked.FalknerSkan.FSScale.scale hc tF tP tQ'
  have hm := Checked.FalknerSkan.FSScale.mapsTo_div hc
  have hinv1 : 1 / a < 1 / lo := one_div_lt_one_div_of_lt (by linarith) hlo_lt
  have hinv2 : 1 / hi < 1 / a := one_div_lt_one_div_of_lt ha0 ha_lt
  refine ⟨-(1 / a), by linarith, by linarith,
    fun s => Real.sqrt a * F (s / Real.sqrt a), fun s => P (s / Real.sqrt a),
    fun s => Q (s / Real.sqrt a) / Real.sqrt a, A, B, fun s hs => ?_,
    by simp [hF0], by simp only [zero_div, hP0]; norm_num, by simp [hQ0], Checked.FalknerSkan.FSScale.scale_lim hc hlim,
    fun s hs => div_pos (hqpos _ (div_pos hs hc)) hc, fun M => ?_⟩
  · refine (C s hs).congr_deriv ?_
    rw [hc2]
    field_simp
  · have hd := (tendsto_id.atTop_div_const hc).eventually (hdec (M * Real.sqrt a))
    filter_upwards [hd] with s hs
    simp only [id] at hs
    rw [le_div_iff₀ hc]
    linarith

end Checked.FSSep.RecedeSep
