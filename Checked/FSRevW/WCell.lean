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
import Checked.Sim.QPoly
import Checked.Sim.OneSided3
import Checked.FSSep.SBase
import Checked.FSSep.SCellWC
import Checked.FSRev.RCell
import Checked.FSRevW.WBase

/-! Falkner–Skan adverse pressure gradient with a free scaled coefficient and a free shear clamp level: weighted one-sided validated cells of the clamped field, every numeric side condition decided by kernel evaluation over the rationals, and the segment lemmas of the reversed-flow chains. Ported from `Checked/FSSep/SCellWC.lean` and `Checked/FSRev/RCell.lean` by `runs/2026-11-13T0628Z/scripts/port_wcell.py` (the clamp level of the shear component is a parameter; the cell data, side and end conditions are reused). Module `WCell`, run 2026-11-13T0628Z. -/

namespace Checked.FSRevW.WCell
open Set Checked.Sim Checked.Sim.QPoly Checked.Sim.OneSided3 Checked.FSNeg.NBase Checked.FSSep.SBase
  Checked.FSSep.SCellWC Checked.FSRev.RBase Checked.FSRev.RCell Checked.FSRevW.WBase

/-- All hypotheses of the weighted cell step except the solution's own, over ℚ. -/
def CellPropW (K T QC : ℚ) (c : Cell) : Prop :=
  0 ≤ c.t0 ∧ c.t0 + c.h ≤ T ∧ 0 < c.h ∧ 0 < c.w1 ∧ 0 < c.w2 ∧ 0 ≤ c.μ ∧ c.μ * c.h < 1 ∧
  0 < c.δ ∧ 0 < c.ε ∧
  c.w1 * qabs (qsub (qderiv c.pg) c.pp) c.h ^ 2 + c.w2 * qabs (qsub (qderiv c.pp) c.pq) c.h ^ 2
    + qabs (defect3 K c) c.h ^ 2 < c.ε ^ 2 ∧
  0 ≤ c.r1 ∧ c.B ^ 2 ≤ c.w1 * c.r1 ^ 2 ∧ 0 ≤ c.r2 ∧ c.B ^ 2 ≤ c.w2 * c.r2 ^ 2 ∧
  psdOK c.μ c.w1 c.w2 (K * mlo c) (K * qlo c) (-(2 * phi c + c.r2)) ∧
  psdOK c.μ c.w1 c.w2 (K * mlo c) (K * qlo c) (-(2 * plo c - c.r2)) ∧
  psdOK c.μ c.w1 c.w2 (K * mlo c) (K * qhi c) (-(2 * phi c + c.r2)) ∧
  psdOK c.μ c.w1 c.w2 (K * mlo c) (K * qhi c) (-(2 * plo c - c.r2)) ∧
  (c.δ + c.ε * c.h) / (1 - c.μ * c.h) ≤ c.B ∧
  -(c.t0 + 2) < glo c - c.r1 ∧ ghi c + c.r1 < c.t0 + 2 ∧ -2 < plo c - c.r2 ∧ phi c + c.r2 < 2 ∧
  -QC < qlo c - c.B ∧ qhi c + c.B < QC ∧ 0 ≤ K

instance (K T QC : ℚ) (c : Cell) : Decidable (CellPropW K T QC c) := by
  unfold CellPropW psdOK; infer_instance

/-- `CellPropW` as a Boolean, for evaluation by the kernel. -/
def cellOKW (K T QC : ℚ) (c : Cell) : Bool := decide (CellPropW K T QC c)

theorem cellOKW_basic {K T QC : ℚ} (c : Cell) (hok : cellOKW K T QC c = true) :
    0 ≤ c.t0 ∧ c.t0 + c.h ≤ T ∧ 0 < c.h := by
  obtain ⟨k1, k2, k3, -⟩ : CellPropW K T QC c := of_decide_eq_true hok
  exact ⟨k1, k2, k3⟩

theorem cell_posW {K T QC : ℚ} (c : Cell) (hok : cellOKW K T QC c = true) :
    (0 : ℝ) < c.w1 ∧ (0 : ℝ) < c.w2 ∧ (0 : ℝ) < c.B ∧ (0 : ℝ) ≤ c.r2 ∧
      (c.B : ℝ) ^ 2 ≤ c.w2 * (c.r2 : ℝ) ^ 2 := by
  obtain ⟨-, -, k3, kw1, kw2, -, kμh, kδ, kε, -, -, -, kr2, kBr2, -, -, -, -, kB, -⟩ :
    CellPropW K T QC c := of_decide_eq_true hok
  have h1 : (0 : ℚ) < 1 - c.μ * c.h := by linarith
  have h2 : (0 : ℚ) < (c.δ + c.ε * c.h) / (1 - c.μ * c.h) :=
    div_pos (by nlinarith) h1
  refine ⟨by exact_mod_cast kw1, by exact_mod_cast kw2, by exact_mod_cast h2.trans_le kB,
    by exact_mod_cast kr2, by exact_mod_cast kBr2⟩

/-- The solution hypotheses on [a, T]. -/
def SolW (K C T a : ℝ) (g p q : ℝ → ℝ) : Prop :=
  (∀ t ∈ Icc a T, HasDerivWithinAt g (cl 2 (p t)) (Icc 0 T) t) ∧
  (∀ t ∈ Icc a T, HasDerivWithinAt p (cl C (q t)) (Icc 0 T) t) ∧
  (∀ t ∈ Icc a T, HasDerivWithinAt q (-(K * cl (max t 0 + 2) (g t) * cl C (q t)) + 1 - cl 2 (p t) ^ 2)
    (Icc 0 T) t)

theorem SolW.mono {K C T a b : ℝ} {g p q : ℝ → ℝ} (h : SolW K C T a g p q) (hab : a ≤ b) :
    SolW K C T b g p q :=
  ⟨fun t ht => h.1 t ⟨hab.trans ht.1, ht.2⟩, fun t ht => h.2.1 t ⟨hab.trans ht.1, ht.2⟩,
    fun t ht => h.2.2 t ⟨hab.trans ht.1, ht.2⟩⟩

set_option maxHeartbeats 1600000 in
/-- One validated weighted cell from its Boolean check: the enclosure on the whole cell. -/
theorem cell_allW {K T QC : ℚ} (c : Cell) (hok : cellOKW K T QC c = true) {g p q : ℝ → ℝ}
    (hs : SolW (K : ℝ) (QC : ℝ) T c.t0 g p q) (h0 : InBox c g p q) :
    ∀ t ∈ Icc (c.t0 : ℝ) (c.t0 + c.h),
      V c.w1 c.w2 (g t - evalQ c.pg (t - c.t0)) (p t - evalQ c.pp (t - c.t0))
        (q t - evalQ c.pq (t - c.t0)) ≤ (c.B : ℝ) ^ 2 := by
  obtain ⟨k1, k2, k3, kw1, kw2, kμ, kμh, kδ, kε, kdef, kr1, kBr, kr2, kBr2, kc1, kc2, kc3, kc4, kB, kx1, kx2, kx3, kx4, kx5, kx6, kK⟩ :
    CellPropW K T QC c := of_decide_eq_true hok
  have hT2 : ((c.t0 + c.h : ℚ) : ℝ) ≤ (T : ℝ) := by exact_mod_cast k2
  push_cast at hT2
  have ht0 : (0 : ℝ) ≤ c.t0 := by exact_mod_cast k1
  have hh : (0 : ℝ) < c.h := by exact_mod_cast k3
  have hw1 : (0 : ℝ) < c.w1 := by exact_mod_cast kw1
  have hw2 : (0 : ℝ) < c.w2 := by exact_mod_cast kw2
  have hμ : (0 : ℝ) ≤ c.μ := by exact_mod_cast kμ
  have hμh : (c.μ : ℝ) * c.h < 1 := by exact_mod_cast kμh
  have hδ : (0 : ℝ) < c.δ := by exact_mod_cast kδ
  have hε : (0 : ℝ) < c.ε := by exact_mod_cast kε
  have hr1 : (0 : ℝ) ≤ c.r1 := by exact_mod_cast kr1
  have hBr : (c.B : ℝ) ^ 2 ≤ c.w1 * (c.r1 : ℝ) ^ 2 := by exact_mod_cast kBr
  have hr2 : (0 : ℝ) ≤ c.r2 := by exact_mod_cast kr2
  have hBr2 : (c.B : ℝ) ^ 2 ≤ c.w2 * (c.r2 : ℝ) ^ 2 := by exact_mod_cast kBr2
  have hdef : (c.w1 : ℝ) * ((qabs (qsub (qderiv c.pg) c.pp) c.h : ℚ) : ℝ) ^ 2
      + c.w2 * ((qabs (qsub (qderiv c.pp) c.pq) c.h : ℚ) : ℝ) ^ 2
      + ((qabs (defect3 K c) c.h : ℚ) : ℝ) ^ 2 < (c.ε : ℝ) ^ 2 := by exact_mod_cast kdef
  have hK : (0 : ℝ) ≤ (K : ℝ) := by exact_mod_cast kK
  have hBq : (((c.δ + c.ε * c.h) / (1 - c.μ * c.h) : ℚ) : ℝ) ≤ (c.B : ℝ) := by exact_mod_cast kB
  push_cast at hBq
  have hsub : Icc (c.t0 : ℝ) (c.t0 + c.h) ⊆ Icc 0 (T : ℝ) :=
    Icc_subset_Icc ht0 hT2
  have hsub' : Icc (c.t0 : ℝ) (c.t0 + c.h) ⊆ Icc (c.t0 : ℝ) T := Icc_subset_Icc le_rfl hT2
  have hnh : ∀ t ∈ Ico (c.t0 : ℝ) (c.t0 + c.h), Icc (0 : ℝ) T ∈ nhdsWithin t (Ici t) := fun t ht =>
    Icc_mem_nhdsGE_of_mem ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hlo : ∀ σ ∈ Icc (0 : ℝ) c.h, ((c.pg.headD 0 - c.h * qabs c.pg.tail c.h : ℚ) : ℝ) ≤ evalQ c.pg σ :=
    fun σ hσ => lower_q c.pg (h := c.h) hσ.1 hσ.2
  have hql : ∀ σ ∈ Icc (0 : ℝ) c.h, ((qlo c : ℚ) : ℝ) ≤ evalQ c.pq σ :=
    fun σ hσ => lower_q c.pq (h := c.h) hσ.1 hσ.2
  have hqh : ∀ σ ∈ Icc (0 : ℝ) c.h, evalQ c.pq σ ≤ ((qhi c : ℚ) : ℝ) :=
    fun σ hσ => upper_q c.pq (h := c.h) hσ.1 hσ.2
  have hpl : ∀ σ ∈ Icc (0 : ℝ) c.h, ((plo c : ℚ) : ℝ) ≤ evalQ c.pp σ :=
    fun σ hσ => lower_q c.pp (h := c.h) hσ.1 hσ.2
  have hph : ∀ σ ∈ Icc (0 : ℝ) c.h, evalQ c.pp σ ≤ ((phi c : ℚ) : ℝ) :=
    fun σ hσ => upper_q c.pp (h := c.h) hσ.1 hσ.2
  have hB0 : (0 : ℝ) ≤ c.B := (cell_posW c hok).2.2.1.le
  have x1 : (-(c.t0 + 2) : ℝ) < ((glo c - c.r1 : ℚ) : ℝ) := by exact_mod_cast kx1
  have x2 : ((ghi c + c.r1 : ℚ) : ℝ) < (c.t0 + 2 : ℝ) := by exact_mod_cast kx2
  have x3 : (-2 : ℝ) < ((plo c - c.r2 : ℚ) : ℝ) := by exact_mod_cast kx3
  have x4 : ((phi c + c.r2 : ℚ) : ℝ) < 2 := by exact_mod_cast kx4
  have x5 : (-(QC : ℝ)) < ((qlo c - c.B : ℚ) : ℝ) := by exact_mod_cast kx5
  have x6 : ((qhi c + c.B : ℚ) : ℝ) < (QC : ℝ) := by exact_mod_cast kx6
  push_cast at x1 x2 x3 x4 x5 x6
  have hgl : ∀ σ ∈ Icc (0 : ℝ) c.h, ((glo c : ℚ) : ℝ) ≤ evalQ c.pg σ :=
    fun σ hσ => lower_q c.pg (h := c.h) hσ.1 hσ.2
  have hgh : ∀ σ ∈ Icc (0 : ℝ) c.h, evalQ c.pg σ ≤ ((ghi c : ℚ) : ℝ) :=
    fun σ hσ => upper_q c.pg (h := c.h) hσ.1 hσ.2
  -- inside the ball the clamps are inactive
  have cl1 : ∀ t ∈ Icc (c.t0 : ℝ) (c.t0 + c.h), ∀ y : ℝ, |y - evalQ c.pg (t - c.t0)| ≤ c.r1 →
      cl (max t 0 + 2) y = y := by
    intro t ht y hy
    have hσ : t - c.t0 ∈ Icc (0 : ℝ) c.h := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have a1 := hgl _ hσ; have a2 := hgh _ hσ
    have hm : (c.t0 : ℝ) ≤ max t 0 := le_trans ht.1 (le_max_left _ _)
    apply cl_of_abs_le; rw [abs_le]
    constructor <;> linarith [(abs_le.1 hy).1, (abs_le.1 hy).2]
  have cl2 : ∀ t ∈ Icc (c.t0 : ℝ) (c.t0 + c.h), ∀ y : ℝ, |y - evalQ c.pp (t - c.t0)| ≤ c.r2 →
      cl 2 y = y := by
    intro t ht y hy
    have hσ : t - c.t0 ∈ Icc (0 : ℝ) c.h := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have a1 := hpl _ hσ; have a2 := hph _ hσ
    apply cl_of_abs_le; rw [abs_le]
    constructor <;> linarith [(abs_le.1 hy).1, (abs_le.1 hy).2]
  have cl3 : ∀ t ∈ Icc (c.t0 : ℝ) (c.t0 + c.h), ∀ y : ℝ, |y - evalQ c.pq (t - c.t0)| ≤ c.B →
      cl (QC : ℝ) y = y := by
    intro t ht y hy
    have hσ : t - c.t0 ∈ Icc (0 : ℝ) c.h := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have a1 := hql _ hσ; have a2 := hqh _ hσ
    apply cl_of_abs_le; rw [abs_le]
    constructor <;> linarith [(abs_le.1 hy).1, (abs_le.1 hy).2]
  have key := onesided3_cell_t (F1 := fun _ _ y2 _ => cl 2 y2) (F2 := fun _ _ _ y3 => cl (QC : ℝ) y3)
    (F3 := fun t y1 y2 y3 => -((K : ℝ) * cl (max t 0 + 2) y1 * cl (QC : ℝ) y3) + 1 - cl 2 y2 ^ 2) (f1 := g) (f2 := p) (f3 := q)
    (g1 := fun t => evalQ c.pg (t - c.t0)) (g2 := fun t => evalQ c.pp (t - c.t0))
    (g3 := fun t => evalQ c.pq (t - c.t0))
    (G1 := fun t => dEvalQ c.pg (t - c.t0)) (G2 := fun t => dEvalQ c.pp (t - c.t0))
    (G3 := fun t => dEvalQ c.pq (t - c.t0))
    (a := c.t0) (b := c.t0 + c.h) (w1 := c.w1) (w2 := c.w2) (μ := c.μ) (ε := c.ε) (δ := c.δ)
    (B := c.B)
    (by linarith) hw1 hw2 hμ hε hδ
    (fun t ht => ((hs.1 t (hsub' ht)).continuousWithinAt).mono hsub)
    (fun t ht => ((hs.2.1 t (hsub' ht)).continuousWithinAt).mono hsub)
    (fun t ht => ((hs.2.2 t (hsub' ht)).continuousWithinAt).mono hsub)
    ((continuous_evalQ c.pg).comp (continuous_sub_right _)).continuousOn
    ((continuous_evalQ c.pp).comp (continuous_sub_right _)).continuousOn
    ((continuous_evalQ c.pq).comp (continuous_sub_right _)).continuousOn
    (fun t ht => (hs.1 t (hsub' (Ico_subset_Icc_self ht))).mono_of_mem_nhdsWithin (hnh t ht))
    (fun t ht => (hs.2.1 t (hsub' (Ico_subset_Icc_self ht))).mono_of_mem_nhdsWithin (hnh t ht))
    (fun t ht => (hs.2.2 t (hsub' (Ico_subset_Icc_self ht))).mono_of_mem_nhdsWithin (hnh t ht))
    (fun t _ => ((hasDerivAt_evalQ c.pg _).comp_sub_const t _).hasDerivWithinAt)
    (fun t _ => ((hasDerivAt_evalQ c.pp _).comp_sub_const t _).hasDerivWithinAt)
    (fun t _ => ((hasDerivAt_evalQ c.pq _).comp_sub_const t _).hasDerivWithinAt)
    (fun t ht => by
      have hσ : t - c.t0 ∈ Icc (0 : ℝ) c.h := ⟨by linarith [ht.1], by linarith [ht.2]⟩
      have ht' : t ∈ Icc (c.t0 : ℝ) (c.t0 + c.h) := Ico_subset_Icc_self ht
      rw [cl1 t ht' _ (by simpa using hr1), cl2 t ht' _ (by simpa using hr2),
        cl3 t ht' _ (by simpa using hB0)]
      have d1 := abs_le_qabs (qsub (qderiv c.pg) c.pp) hσ.1 hσ.2
      have d2 := abs_le_qabs (qsub (qderiv c.pp) c.pq) hσ.1 hσ.2
      have d3 := abs_le_qabs (defect3 K c) hσ.1 hσ.2
      rw [evalQ_qsub, ← dEvalQ_eq] at d1 d2
      rw [← defect3_eval K] at d3
      have s1 := sq_le_sq' (abs_le.1 d1).1 (abs_le.1 d1).2
      have s2 := sq_le_sq' (abs_le.1 d2).1 (abs_le.1 d2).2
      have s3 := sq_le_sq' (abs_le.1 d3).1 (abs_le.1 d3).2
      have e3 : dEvalQ c.pq (t - c.t0) - (-((K : ℝ) * evalQ c.pg (t - c.t0) * evalQ c.pq (t - c.t0)) + 1
            - evalQ c.pp (t - c.t0) ^ 2)
          = dEvalQ c.pq (t - c.t0) + (K : ℝ) * evalQ c.pg (t - c.t0) * evalQ c.pq (t - c.t0) - 1
            + evalQ c.pp (t - c.t0) ^ 2 := by ring
      simp only [e3]
      nlinarith [mul_le_mul_of_nonneg_left s1 hw1.le, mul_le_mul_of_nonneg_left s2 hw2.le])
    (fun t ht y1 y2 y3 hy => by
      have hσ : t - c.t0 ∈ Icc (0 : ℝ) c.h := ⟨by linarith [ht.1], by linarith [ht.2]⟩
      have n1 := mul_nonneg hw1.le (sq_nonneg (y1 - evalQ c.pg (t - c.t0)))
      have n2 := mul_nonneg hw2.le (sq_nonneg (y2 - evalQ c.pp (t - c.t0)))
      have n3 := sq_nonneg (y3 - evalQ c.pq (t - c.t0))
      have he1 : |y1 - evalQ c.pg (t - c.t0)| ≤ c.r1 := comp_le hw1 hr1 (by linarith) hBr
      have he2 : |y2 - evalQ c.pp (t - c.t0)| ≤ c.r2 := comp_le hw2 hr2 (by linarith) hBr2
      have he3 : |y3 - evalQ c.pq (t - c.t0)| ≤ c.B :=
        comp_le (w := 1) (B := (c.B : ℝ)) one_pos hB0 (by linarith) (by linarith)
      have ht' : t ∈ Icc (c.t0 : ℝ) (c.t0 + c.h) := Ico_subset_Icc_self ht
      rw [cl1 t ht' _ he1, cl2 t ht' _ he2, cl3 t ht' _ he3,
        cl1 t ht' _ (by simpa using hr1), cl2 t ht' _ (by simpa using hr2),
        cl3 t ht' _ (by simpa using hB0)]
      have hm : ((K * mlo c : ℚ) : ℝ) ≤ (K : ℝ) * y1 := by
        have := hlo _ hσ
        have hy : ((mlo c : ℚ) : ℝ) ≤ y1 := by
          unfold mlo; push_cast at this ⊢
          linarith [(abs_le.1 he1).1]
        push_cast; exact mul_le_mul_of_nonneg_left hy hK
      have hs1 : ((-(2 * phi c + c.r2) : ℚ) : ℝ) ≤ -(y2 + evalQ c.pp (t - c.t0)) := by
        have := hph _ hσ
        push_cast
        linarith [(abs_le.1 he2).2]
      have hs2 : -(y2 + evalQ c.pp (t - c.t0)) ≤ ((-(2 * plo c - c.r2) : ℚ) : ℝ) := by
        have := hpl _ hσ
        push_cast
        linarith [(abs_le.1 he2).1]
      have hql2 : ((K * qlo c : ℚ) : ℝ) ≤ (K : ℝ) * evalQ c.pq (t - c.t0) := by
        have := hql _ hσ; push_cast; exact mul_le_mul_of_nonneg_left this hK
      have hqh2 : (K : ℝ) * evalQ c.pq (t - c.t0) ≤ ((K * qhi c : ℚ) : ℝ) := by
        have := hqh _ hσ; push_cast; exact mul_le_mul_of_nonneg_left this hK
      have := os_neg (K := (K : ℝ)) (μ := c.μ) (w1 := c.w1) (w2 := c.w2) (m := ((K * mlo c : ℚ) : ℝ))
        (ql := ((K * qlo c : ℚ) : ℝ)) (qh := ((K * qhi c : ℚ) : ℝ))
        (sl := ((-(2 * phi c + c.r2) : ℚ) : ℝ)) (sh := ((-(2 * plo c - c.r2) : ℚ) : ℝ))
        (P1 := evalQ c.pg (t - c.t0)) (P2 := evalQ c.pp (t - c.t0))
        (P3 := evalQ c.pq (t - c.t0)) (y1 := y1) (y2 := y2) (y3 := y3)
        (quad_of_psd kc1) (quad_of_psd kc2) (quad_of_psd kc3) (quad_of_psd kc4)
        hm hql2 hqh2 hs1 hs2
      simpa using this)
    (by
      simp only [sub_self, evalQ_zero_head]
      exact h0)
    (R_le hδ hε hμ hμh hBq ⟨by linarith, le_rfl⟩)
  intro t ht
  have e := key t ht
  have hpos : (0 : ℝ) ≤ (c.δ + c.ε * (t - c.t0)) * Real.exp (c.μ * (t - c.t0)) :=
    mul_nonneg (by nlinarith [ht.1]) (Real.exp_pos _).le
  have hsq := pow_le_pow_left₀ hpos (R_le hδ hε hμ hμh hBq ht) 2
  unfold V
  exact e.trans hsq

/-- One validated weighted cell from its Boolean check: the enclosure at the cell's end. -/
theorem cell_wW {K T QC : ℚ} (c : Cell) (hok : cellOKW K T QC c = true) {g p q : ℝ → ℝ}
    (hs : SolW (K : ℝ) (QC : ℝ) T c.t0 g p q) (h0 : InBox c g p q) : AtEnd c g p q := by
  have hh : (0 : ℝ) < c.h := by exact_mod_cast (cellOKW_basic c hok).2.2
  have e := cell_allW c hok hs h0 (c.t0 + c.h) ⟨by linarith, le_rfl⟩
  unfold AtEnd
  simp only [add_sub_cancel_left] at e
  simpa only [qeval_cast] using e

theorem sideU_specW {K T QC : ℚ} (c : Cell) (hok : cellOKW K T QC c = true) (hside : sideU c = true)
    {g p q : ℝ → ℝ} (hs : SolW (K : ℝ) (QC : ℝ) T c.t0 g p q) (h0 : InBox c g p q) :
    ∀ t ∈ Icc (c.t0 : ℝ) (c.t0 + c.h), p t < 1 := by
  obtain ⟨-, -, -, kw1, kw2, -, -, -, -, -, -, -, kr2, kBr2, -⟩ : CellPropW K T QC c := of_decide_eq_true hok
  have hw1 : (0 : ℝ) < c.w1 := by exact_mod_cast kw1
  have hw2 : (0 : ℝ) < c.w2 := by exact_mod_cast kw2
  have hr2 : (0 : ℝ) ≤ c.r2 := by exact_mod_cast kr2
  have hBr2 : (c.B : ℝ) ^ 2 ≤ c.w2 * (c.r2 : ℝ) ^ 2 := by exact_mod_cast kBr2
  have hU : ((phi c + c.r2 : ℚ) : ℝ) < 1 := by exact_mod_cast (of_decide_eq_true hside)
  push_cast at hU
  intro t ht
  have e := cell_allW c hok hs h0 t ht
  unfold V at e
  have n1 := mul_nonneg hw1.le (sq_nonneg (g t - evalQ c.pg (t - c.t0)))
  have n3 := sq_nonneg (q t - evalQ c.pq (t - c.t0))
  have he2 : |p t - evalQ c.pp (t - c.t0)| ≤ c.r2 := comp_le hw2 hr2 (by linarith) hBr2
  have hσ : t - c.t0 ∈ Icc (0 : ℝ) c.h := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hp := upper_q c.pp (h := c.h) hσ.1 hσ.2
  have hphi : ((phi c : ℚ) : ℝ) = ((c.pp.headD 0 + c.h * qabs c.pp.tail c.h : ℚ) : ℝ) := rfl
  rw [← hphi] at hp
  linarith [(abs_le.1 he2).2]

theorem sideO_specW {K T QC : ℚ} (c : Cell) (hok : cellOKW K T QC c = true) (hside : sideO c = true)
    {g p q : ℝ → ℝ} (hs : SolW (K : ℝ) (QC : ℝ) T c.t0 g p q) (h0 : InBox c g p q) :
    ∀ t ∈ Icc (c.t0 : ℝ) (c.t0 + c.h), 0 < q t := by
  obtain ⟨-, -, -, kw1, kw2, -⟩ : CellPropW K T QC c := of_decide_eq_true hok
  have hw1 : (0 : ℝ) < c.w1 := by exact_mod_cast kw1
  have hw2 : (0 : ℝ) < c.w2 := by exact_mod_cast kw2
  have hO : (0 : ℝ) < ((qlo c - c.B : ℚ) : ℝ) := by exact_mod_cast (of_decide_eq_true hside)
  push_cast at hO
  intro t ht
  have e := cell_allW c hok hs h0 t ht
  unfold V at e
  have n1 := mul_nonneg hw1.le (sq_nonneg (g t - evalQ c.pg (t - c.t0)))
  have n2 := mul_nonneg hw2.le (sq_nonneg (p t - evalQ c.pp (t - c.t0)))
  have hB0 : (0 : ℝ) ≤ c.B := (cell_posW c hok).2.2.1.le
  have he3 : |q t - evalQ c.pq (t - c.t0)| ≤ c.B :=
    comp_le (w := 1) (B := (c.B : ℝ)) one_pos hB0 (by linarith) (by linarith)
  have hσ : t - c.t0 ∈ Icc (0 : ℝ) c.h := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hq := lower_q c.pq (h := c.h) hσ.1 hσ.2
  have hqlo : ((qlo c : ℚ) : ℝ) = ((c.pq.headD 0 - c.h * qabs c.pq.tail c.h : ℚ) : ℝ) := rfl
  rw [← hqlo] at hq
  linarith [(abs_le.1 he3).1]

/-- A chain of cells inside [0, T], each satisfying `side`, whose last cell satisfies `term`. -/
def chainW (K T QC : ℚ) (side term : Cell → Bool) : List Cell → Bool
  | [] => false
  | [c] => cellOKW K T QC c && side c && term c
  | c :: d :: l => cellOKW K T QC c && side c && linkOK c d && chainW K T QC side term (d :: l)

/-- A chain from its Boolean check: some last cell `e` satisfies `term`, every solution entering
the first cell's ball is enclosed at `e`'s end, and `Φ` holds from the first cell's start to
`e`'s end. -/
theorem chainW_gen {K T QC : ℚ} {side term : Cell → Bool}
    {Φ : (ℝ → ℝ) → (ℝ → ℝ) → (ℝ → ℝ) → ℝ → Prop}
    (hside : ∀ c, cellOKW K T QC c = true → side c = true → ∀ {g p q : ℝ → ℝ}, SolW (K : ℝ) (QC : ℝ) T c.t0 g p q →
      InBox c g p q → ∀ t ∈ Icc (c.t0 : ℝ) (c.t0 + c.h), Φ g p q t) :
    ∀ (l : List Cell) (c : Cell), chainW K T QC side term (c :: l) = true →
    ∀ {g p q : ℝ → ℝ}, SolW (K : ℝ) (QC : ℝ) T c.t0 g p q → InBox c g p q →
    ∃ e : Cell, cellOKW K T QC e = true ∧ term e = true ∧ AtEnd e g p q ∧
      ∀ t ∈ Icc (c.t0 : ℝ) (e.t0 + e.h), Φ g p q t := by
  intro l
  induction l with
  | nil =>
    intro c hok g p q hs h0
    simp only [chainW, Bool.and_eq_true] at hok
    exact ⟨c, hok.1.1, hok.2, cell_wW c hok.1.1 hs h0, hside c hok.1.1 hok.1.2 hs h0⟩
  | cons d l ih =>
    intro c hok g p q hs h0
    simp only [chainW, Bool.and_eq_true] at hok
    obtain ⟨⟨⟨k1, ks⟩, kl⟩, krest⟩ := hok
    have he := cell_wW c k1 hs h0
    obtain ⟨hdt, hbox⟩ := link_box kl he
    have hh : (0 : ℝ) < c.h := by exact_mod_cast (cellOKW_basic c k1).2.2
    have hc := hside c k1 ks hs h0
    obtain ⟨e, hke, hte, hend, hΦ⟩ := ih d krest (hs.mono (by rw [hdt]; linarith)) hbox
    refine ⟨e, hke, hte, hend, fun t ht => ?_⟩
    rcases le_total t (c.t0 + c.h) with h1 | h1
    · exact hc t ⟨ht.1, h1⟩
    · exact hΦ t ⟨by rw [hdt]; exact h1, ht.2⟩

theorem chainW_head {K T QC : ℚ} {side term : Cell → Bool} (c : Cell) (l : List Cell)
    (h : chainW K T QC side term (c :: l) = true) : cellOKW K T QC c = true := by
  cases l with
  | nil => simp only [chainW, Bool.and_eq_true] at h; exact h.1.1
  | cons _ _ => simp only [chainW, Bool.and_eq_true] at h; exact h.1.1.1

/-- A segment ending in the input ball of `d`, with `Φ` on [c.t0, d.t0]; solution hypotheses on
the whole of [0, T]. -/
theorem segW_q0 {K T QC : ℚ} {side : Cell → Bool} {Φ : (ℝ → ℝ) → (ℝ → ℝ) → (ℝ → ℝ) → ℝ → Prop}
    (hside : ∀ c, cellOKW K T QC c = true → side c = true → ∀ {g p q : ℝ → ℝ}, SolW (K : ℝ) (QC : ℝ) T c.t0 g p q →
      InBox c g p q → ∀ t ∈ Icc (c.t0 : ℝ) (c.t0 + c.h), Φ g p q t)
    (d : Cell) (l : List Cell) (c : Cell)
    (hok : chainW K T QC side (fun e => linkOK e d) (c :: l) = true) {g p q : ℝ → ℝ}
    (hs : SolW (K : ℝ) (QC : ℝ) T 0 g p q) (h0 : InBox c g p q) :
    InBox d g p q ∧ ∀ t ∈ Icc (c.t0 : ℝ) d.t0, Φ g p q t := by
  have k := (cellOKW_basic c (chainW_head c l hok)).1
  obtain ⟨e, -, he, hend, hΦ⟩ := chainW_gen hside l c hok (hs.mono (by exact_mod_cast k)) h0
  obtain ⟨hdt, hbox⟩ := link_box he hend
  exact ⟨hbox, by rw [hdt]; exact hΦ⟩

/-- A final overshoot segment: p(T) > 1 and `Φ` on [c.t0, T]. -/
theorem endSOW_q0 {K T QC : ℚ} {side : Cell → Bool} {Φ : (ℝ → ℝ) → (ℝ → ℝ) → (ℝ → ℝ) → ℝ → Prop}
    (hside : ∀ c, cellOKW K T QC c = true → side c = true → ∀ {g p q : ℝ → ℝ}, SolW (K : ℝ) (QC : ℝ) T c.t0 g p q →
      InBox c g p q → ∀ t ∈ Icc (c.t0 : ℝ) (c.t0 + c.h), Φ g p q t)
    (l : List Cell) (c : Cell) (hok : chainW K T QC side (endO T) (c :: l) = true) {g p q : ℝ → ℝ}
    (hs : SolW (K : ℝ) (QC : ℝ) T 0 g p q) (h0 : InBox c g p q) :
    1 < p T ∧ ∀ t ∈ Icc (c.t0 : ℝ) T, Φ g p q t := by
  have k := (cellOKW_basic c (chainW_head c l hok)).1
  obtain ⟨e, hke, he, hend, hΦ⟩ := chainW_gen hside l c hok (hs.mono (by exact_mod_cast k)) h0
  obtain ⟨kT, kp⟩ := of_decide_eq_true he
  obtain ⟨hw1, hw2, hB, hr2, hBr2⟩ := cell_posW e hke
  have hT : ((e.t0 + e.h : ℚ) : ℝ) = (T : ℝ) := by exact_mod_cast kT
  push_cast at hT
  have kp' : (1 : ℝ) < ((qeval e.pp e.h - e.r2 : ℚ) : ℝ) := by exact_mod_cast kp
  push_cast at kp'
  unfold AtEnd V at hend
  rw [hT] at hend hΦ
  refine ⟨?_, hΦ⟩
  have n1 := mul_nonneg hw1.le (sq_nonneg (g T - ((qeval e.pg e.h : ℚ) : ℝ)))
  have n3 := sq_nonneg (q T - ((qeval e.pq e.h : ℚ) : ℝ))
  have b2 : |p T - ((qeval e.pp e.h : ℚ) : ℝ)| ≤ e.r2 := comp_le hw2 hr2 (by linarith) hBr2
  linarith [(abs_le.1 b2).1]

/-- A final overshoot segment: p(T) > 1 (no side condition carried). -/
theorem endOW_q0 {K T QC : ℚ} (l : List Cell) (c : Cell) (hok : chainW K T QC sideT (endO T) (c :: l) = true)
    {g p q : ℝ → ℝ} (hs : SolW (K : ℝ) (QC : ℝ) T 0 g p q) (h0 : InBox c g p q) : 1 < p T :=
  (endSOW_q0 (Φ := fun _ _ _ _ => True) (fun _ _ _ _ _ _ _ _ _ _ => trivial) l c hok hs h0).1

/-- Enclosure of the three components on a checked cell. -/
theorem enclW {K T QC : ℚ} (c : Cell) (hok : cellOKW K T QC c = true) {g p q : ℝ → ℝ}
    (hs : SolW (K : ℝ) (QC : ℝ) T c.t0 g p q) (h0 : InBox c g p q) (t : ℝ) (ht : t ∈ Icc (c.t0 : ℝ) (c.t0 + c.h)) :
    |g t - evalQ c.pg (t - c.t0)| ≤ c.r1 ∧ |p t - evalQ c.pp (t - c.t0)| ≤ c.r2 ∧
      |q t - evalQ c.pq (t - c.t0)| ≤ c.B := by
  obtain ⟨-, -, -, kw1, kw2, -, -, -, -, -, kr1, kBr, kr2, kBr2, -⟩ : CellPropW K T QC c :=
    of_decide_eq_true hok
  have hw1 : (0 : ℝ) < c.w1 := by exact_mod_cast kw1
  have hw2 : (0 : ℝ) < c.w2 := by exact_mod_cast kw2
  have hr1 : (0 : ℝ) ≤ c.r1 := by exact_mod_cast kr1
  have hr2 : (0 : ℝ) ≤ c.r2 := by exact_mod_cast kr2
  have hBr : (c.B : ℝ) ^ 2 ≤ c.w1 * (c.r1 : ℝ) ^ 2 := by exact_mod_cast kBr
  have hBr2 : (c.B : ℝ) ^ 2 ≤ c.w2 * (c.r2 : ℝ) ^ 2 := by exact_mod_cast kBr2
  have hB0 : (0 : ℝ) ≤ c.B := (cell_posW c hok).2.2.1.le
  have e := cell_allW c hok hs h0 t ht
  unfold V at e
  have n1 := mul_nonneg hw1.le (sq_nonneg (g t - evalQ c.pg (t - c.t0)))
  have n2 := mul_nonneg hw2.le (sq_nonneg (p t - evalQ c.pp (t - c.t0)))
  have n3 := sq_nonneg (q t - evalQ c.pq (t - c.t0))
  exact ⟨comp_le hw1 hr1 (by linarith) hBr, comp_le hw2 hr2 (by linarith) hBr2,
    comp_le (w := 1) (B := (c.B : ℝ)) one_pos hB0 (by linarith) (by linarith)⟩

/-- On a checked cell the enclosed solution lies inside the clamps of `vW`. -/
theorem cell_boxW {K T QC : ℚ} (c : Cell) (hok : cellOKW K T QC c = true) {g p q : ℝ → ℝ}
    (hs : SolW (K : ℝ) (QC : ℝ) T c.t0 g p q) (h0 : InBox c g p q) :
    ∀ t ∈ Icc (c.t0 : ℝ) (c.t0 + c.h), |g t| ≤ t + 2 ∧ |p t| ≤ 2 ∧ |q t| ≤ (QC : ℝ) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, kg1, kg2, kp1, kp2, kq1, kq2, -⟩ :
    CellPropW K T QC c := of_decide_eq_true hok
  intro t ht
  obtain ⟨b1, b2, b3⟩ := enclW c hok hs h0 t ht
  have hσ : t - c.t0 ∈ Icc (0 : ℝ) c.h := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have lg := lower_q c.pg (h := c.h) hσ.1 hσ.2
  have ug := upper_q c.pg (h := c.h) hσ.1 hσ.2
  have lp := lower_q c.pp (h := c.h) hσ.1 hσ.2
  have up := upper_q c.pp (h := c.h) hσ.1 hσ.2
  have lq := lower_q c.pq (h := c.h) hσ.1 hσ.2
  have uq := upper_q c.pq (h := c.h) hσ.1 hσ.2
  have kg1' : ((-(c.t0 + 2) : ℚ) : ℝ) < ((glo c - c.r1 : ℚ) : ℝ) := by exact_mod_cast kg1
  have kg2' : ((ghi c + c.r1 : ℚ) : ℝ) < ((c.t0 + 2 : ℚ) : ℝ) := by exact_mod_cast kg2
  have kp1' : ((-2 : ℚ) : ℝ) < ((plo c - c.r2 : ℚ) : ℝ) := by exact_mod_cast kp1
  have kp2' : ((phi c + c.r2 : ℚ) : ℝ) < ((2 : ℚ) : ℝ) := by exact_mod_cast kp2
  have kq1' : ((-QC : ℚ) : ℝ) < ((qlo c - c.B : ℚ) : ℝ) := by exact_mod_cast kq1
  have kq2' : ((qhi c + c.B : ℚ) : ℝ) < ((QC : ℚ) : ℝ) := by exact_mod_cast kq2
  simp only [glo, ghi, plo, phi, qlo, qhi] at kg1' kg2' kp1' kp2' kq1' kq2'
  push_cast at kg1' kg2' kp1' kp2' kq1' kq2' lg ug lp up lq uq
  have a1 := abs_le.1 b1; have a2 := abs_le.1 b2; have a3 := abs_le.1 b3
  refine ⟨abs_le.2 ⟨by linarith [ht.1], by linarith [ht.1]⟩, abs_le.2 ⟨by linarith, by linarith⟩,
    abs_le.2 ⟨by linarith, by linarith⟩⟩

theorem sideP_specW {K T QC : ℚ} (c : Cell) (hok : cellOKW K T QC c = true) (hside : sideP c = true)
    {g p q : ℝ → ℝ} (hs : SolW (K : ℝ) (QC : ℝ) T c.t0 g p q) (h0 : InBox c g p q) :
    ∀ t ∈ Icc (c.t0 : ℝ) (c.t0 + c.h), PhiW (QC : ℝ) g p q t := by
  intro t ht
  refine ⟨cell_boxW c hok hs h0 t ht, ?_⟩
  obtain ⟨-, b2, -⟩ := enclW c hok hs h0 t ht
  have hσ : t - c.t0 ∈ Icc (0 : ℝ) c.h := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have lp := lower_q c.pp (h := c.h) hσ.1 hσ.2
  have k : ((-1 / 2 : ℚ) : ℝ) < ((plo c - c.r2 : ℚ) : ℝ) := by exact_mod_cast (of_decide_eq_true hside)
  simp only [plo] at k
  push_cast at k lp
  linarith [(abs_le.1 b2).1]

/-- The enclosure at the end of a chain ending at `T`. -/
theorem end_enclW {K T QC : ℚ} {side term : Cell → Bool} {Φ : (ℝ → ℝ) → (ℝ → ℝ) → (ℝ → ℝ) → ℝ → Prop}
    (hside : ∀ c, cellOKW K T QC c = true → side c = true → ∀ {g p q : ℝ → ℝ}, SolW (K : ℝ) (QC : ℝ) T c.t0 g p q →
      InBox c g p q → ∀ t ∈ Icc (c.t0 : ℝ) (c.t0 + c.h), Φ g p q t)
    (hterm : ∀ e, term e = true → e.t0 + e.h = T)
    (l : List Cell) (c : Cell) (hok : chainW K T QC side term (c :: l) = true) {g p q : ℝ → ℝ}
    (hs : SolW (K : ℝ) (QC : ℝ) T 0 g p q) (h0 : InBox c g p q) :
    ∃ e : Cell, term e = true ∧
      |g T - ((qeval e.pg e.h : ℚ) : ℝ)| ≤ e.r1 ∧ |p T - ((qeval e.pp e.h : ℚ) : ℝ)| ≤ e.r2 ∧
      |q T - ((qeval e.pq e.h : ℚ) : ℝ)| ≤ e.B ∧ ∀ t ∈ Icc (c.t0 : ℝ) T, Φ g p q t := by
  have k := (cellOKW_basic c (chainW_head c l hok)).1
  obtain ⟨e, hke, he, hend, hΦ⟩ := chainW_gen hside l c hok (hs.mono (by exact_mod_cast k)) h0
  obtain ⟨-, -, -, kw1, kw2, -, -, -, -, -, kr1, kBr, kr2, kBr2, -⟩ : CellPropW K T QC e :=
    of_decide_eq_true hke
  obtain ⟨hw1, hw2, hB, hr2, hBr2⟩ := cell_posW e hke
  have hr1 : (0 : ℝ) ≤ e.r1 := by exact_mod_cast kr1
  have hBr : (e.B : ℝ) ^ 2 ≤ e.w1 * (e.r1 : ℝ) ^ 2 := by exact_mod_cast kBr
  have hT : ((e.t0 + e.h : ℚ) : ℝ) = (T : ℝ) := by exact_mod_cast (hterm e he)
  push_cast at hT
  unfold AtEnd V at hend
  rw [hT] at hend hΦ
  have n1 := mul_nonneg hw1.le (sq_nonneg (g T - ((qeval e.pg e.h : ℚ) : ℝ)))
  have n2 := mul_nonneg hw2.le (sq_nonneg (p T - ((qeval e.pp e.h : ℚ) : ℝ)))
  have n3 := sq_nonneg (q T - ((qeval e.pq e.h : ℚ) : ℝ))
  exact ⟨e, he, comp_le hw1 hr1 (by linarith) hBr, comp_le hw2 hr2 (by linarith) hBr2,
    comp_le (w := 1) (B := (e.B : ℝ)) one_pos hB.le (by linarith) (by linarith), hΦ⟩

theorem endTW_q0 {K T QC : ℚ} {side : Cell → Bool} {Φ : (ℝ → ℝ) → (ℝ → ℝ) → (ℝ → ℝ) → ℝ → Prop}
    (hside : ∀ c, cellOKW K T QC c = true → side c = true → ∀ {g p q : ℝ → ℝ}, SolW (K : ℝ) (QC : ℝ) T c.t0 g p q →
      InBox c g p q → ∀ t ∈ Icc (c.t0 : ℝ) (c.t0 + c.h), Φ g p q t)
    (l : List Cell) (c : Cell) (hok : chainW K T QC side (endT T) (c :: l) = true)
    {g p q : ℝ → ℝ} (hs : SolW (K : ℝ) (QC : ℝ) T 0 g p q) (h0 : InBox c g p q) :
    (0 < g T ∧ g T < 1 ∧ 0 < p T ∧ p T < 1 ∧ 0 < q T ∧ q T < 6 / 5) ∧
      ∀ t ∈ Icc (c.t0 : ℝ) T, Φ g p q t := by
  obtain ⟨e, he, b1, b2, b3, hΦ⟩ := end_enclW hside
    (fun e he => (of_decide_eq_true he).1) l c hok hs h0
  obtain ⟨-, k1, k2, k3, k4, k5, k6⟩ := of_decide_eq_true he
  have k1' : (0 : ℝ) < ((qeval e.pg e.h - e.r1 : ℚ) : ℝ) := by exact_mod_cast k1
  have k2' : ((qeval e.pg e.h + e.r1 : ℚ) : ℝ) < 1 := by exact_mod_cast k2
  have k3' : (0 : ℝ) < ((qeval e.pp e.h - e.r2 : ℚ) : ℝ) := by exact_mod_cast k3
  have k4' : ((qeval e.pp e.h + e.r2 : ℚ) : ℝ) < 1 := by exact_mod_cast k4
  have k5' : (0 : ℝ) < ((qeval e.pq e.h - e.B : ℚ) : ℝ) := by exact_mod_cast k5
  have k6' : ((qeval e.pq e.h + e.B : ℚ) : ℝ) < ((6 / 5 : ℚ) : ℝ) := by exact_mod_cast k6
  push_cast at k1' k2' k3' k4' k5' k6'
  have a1 := abs_le.1 b1; have a2 := abs_le.1 b2; have a3 := abs_le.1 b3
  exact ⟨⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩, hΦ⟩

theorem endSRW_q0 {K T QC : ℚ} {side : Cell → Bool} {Φ : (ℝ → ℝ) → (ℝ → ℝ) → (ℝ → ℝ) → ℝ → Prop}
    (hside : ∀ c, cellOKW K T QC c = true → side c = true → ∀ {g p q : ℝ → ℝ}, SolW (K : ℝ) (QC : ℝ) T c.t0 g p q →
      InBox c g p q → ∀ t ∈ Icc (c.t0 : ℝ) (c.t0 + c.h), Φ g p q t)
    (l : List Cell) (c : Cell) (hok : chainW K T QC side (endSR T) (c :: l) = true)
    {g p q : ℝ → ℝ} (hs : SolW (K : ℝ) (QC : ℝ) T 0 g p q) (h0 : InBox c g p q) :
    (1 / 3 < p T ∧ 0 < q T ∧ q T < 3 * (1 - p T) ∧ 11 / 15 < g T) ∧
      ∀ t ∈ Icc (c.t0 : ℝ) T, Φ g p q t := by
  obtain ⟨e, he, b1, b2, b3, hΦ⟩ := end_enclW hside
    (fun e he => (of_decide_eq_true he).1) l c hok hs h0
  obtain ⟨-, k1, k2, k3, k4⟩ := of_decide_eq_true he
  have k1' : ((1 / 3 : ℚ) : ℝ) < ((qeval e.pp e.h - e.r2 : ℚ) : ℝ) := by exact_mod_cast k1
  have k2' : (0 : ℝ) < ((qeval e.pq e.h - e.B : ℚ) : ℝ) := by exact_mod_cast k2
  have k3' : ((qeval e.pq e.h + e.B : ℚ) : ℝ) < ((3 * (1 - (qeval e.pp e.h + e.r2)) : ℚ) : ℝ) := by
    exact_mod_cast k3
  have k4' : ((11 / 15 : ℚ) : ℝ) < ((qeval e.pg e.h - e.r1 : ℚ) : ℝ) := by exact_mod_cast k4
  push_cast at k1' k2' k3' k4'
  have a1 := abs_le.1 b1; have a2 := abs_le.1 b2; have a3 := abs_le.1 b3
  exact ⟨⟨by linarith, by linarith, by linarith, by linarith⟩, hΦ⟩

end Checked.FSRevW.WCell
