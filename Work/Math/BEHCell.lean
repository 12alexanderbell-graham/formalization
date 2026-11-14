import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Checked.Sim.ODETools
import Checked.Sim.QPoly
import Checked.Math.LECell
import Checked.Math.GCellQ

/-! Bonnor–Ebert sphere, `BEHCell`: validated cells for the isothermal equation in the homology
(Milne) variables u = s e^w / (−w'), v = −s w', which solve s u' = u (3 − u − v), s v' = v (u − 1).
The Lipschitz constant is taken on a box around the cell's Taylor polynomials (not around 0), so
the enclosure grows like a power of the radius instead of exponentially in it. Every side condition,
both defect bounds and the sign invariant of a cell are one proposition over the rationals, decided by
the kernel; a chain of cells is one Boolean. Written by run 2026-11-14T0428Z. -/

namespace Work.Math.BEHCell
open Set Checked.Sim Checked.Sim.QPoly Checked.Math.LECell
open Checked.Math.GCellQ (lo hi lo_le le_hi abs_link icc_glue)

/-- The homology field at radius t. -/
noncomputable def hF (t : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (p.1 * (3 - p.1 - p.2) / t, p.2 * (p.1 - 1) / t)

/-- The box UL ≤ u ≤ UH, VL ≤ v ≤ VH. -/
def box (UL UH VL VH : ℝ) : Set (ℝ × ℝ) := {p | UL ≤ p.1 ∧ p.1 ≤ UH ∧ VL ≤ p.2 ∧ p.2 ≤ VH}

theorem lip_box {t t0 UL UH VL VH L1 L2 K : ℝ} (ht0 : 0 < t0) (ht : t0 ≤ t) (hUL : 0 < UL)
    (hVL : 0 < VL) (hL1a : 3 - 2 * UL - VL ≤ L1) (hL1b : 2 * UH + VH - 3 ≤ L1)
    (hL2a : UH - 1 ≤ L2) (hL2b : 1 - UL ≤ L2) (hK1 : L1 + UH ≤ K * t0) (hK2 : VH + L2 ≤ K * t0)
    (hK0 : 0 ≤ K) :
    LipschitzOnWith (Real.toNNReal K) (hF t) (box UL UH VL VH) := by
  have htp : 0 < t := lt_of_lt_of_le ht0 ht
  refine LipschitzOnWith.of_dist_le_mul fun p hp q hq => ?_
  rw [Real.coe_toNNReal _ hK0]
  simp only [hF, Prod.dist_eq, Real.dist_eq]
  set m := max |p.1 - q.1| |p.2 - q.2|
  have hd1 : |p.1 - q.1| ≤ m := le_max_left _ _
  have hd2 : |p.2 - q.2| ≤ m := le_max_right _ _
  have hm : 0 ≤ m := (abs_nonneg _).trans hd1
  obtain ⟨p1, p2, p3, p4⟩ := hp
  obtain ⟨q1, q2, q3, q4⟩ := hq
  have hKt : K * t0 ≤ K * t := mul_le_mul_of_nonneg_left ht hK0
  refine max_le ?_ ?_
  · have e : p.1 * (3 - p.1 - p.2) / t - q.1 * (3 - q.1 - q.2) / t =
        ((3 - p.1 - q.1 - p.2) * (p.1 - q.1) - q.1 * (p.2 - q.2)) / t := by ring
    rw [e, abs_div, abs_of_pos htp, div_le_iff₀ htp]
    have a1 : |3 - p.1 - q.1 - p.2| ≤ L1 := by rw [abs_le]; constructor <;> linarith
    have a2 : |q.1| ≤ UH := by rw [abs_le]; constructor <;> linarith
    calc |(3 - p.1 - q.1 - p.2) * (p.1 - q.1) - q.1 * (p.2 - q.2)|
        ≤ |(3 - p.1 - q.1 - p.2) * (p.1 - q.1)| + |q.1 * (p.2 - q.2)| := abs_sub _ _
      _ = |3 - p.1 - q.1 - p.2| * |p.1 - q.1| + |q.1| * |p.2 - q.2| := by rw [abs_mul, abs_mul]
      _ ≤ L1 * m + UH * m := by gcongr <;> linarith [abs_nonneg (3 - p.1 - q.1 - p.2)]
      _ = (L1 + UH) * m := by ring
      _ ≤ (K * t) * m := mul_le_mul_of_nonneg_right (by linarith) hm
      _ = K * m * t := by ring
  · have e : p.2 * (p.1 - 1) / t - q.2 * (q.1 - 1) / t =
        (p.2 * (p.1 - q.1) + (q.1 - 1) * (p.2 - q.2)) / t := by ring
    rw [e, abs_div, abs_of_pos htp, div_le_iff₀ htp]
    have a1 : |p.2| ≤ VH := by rw [abs_le]; constructor <;> linarith
    have a2 : |q.1 - 1| ≤ L2 := by rw [abs_le]; constructor <;> linarith
    calc |p.2 * (p.1 - q.1) + (q.1 - 1) * (p.2 - q.2)|
        ≤ |p.2 * (p.1 - q.1)| + |(q.1 - 1) * (p.2 - q.2)| := abs_add_le _ _
      _ = |p.2| * |p.1 - q.1| + |q.1 - 1| * |p.2 - q.2| := by rw [abs_mul, abs_mul]
      _ ≤ VH * m + L2 * m := by gcongr <;> linarith [abs_nonneg (q.1 - 1)]
      _ = (VH + L2) * m := by ring
      _ ≤ (K * t) * m := mul_le_mul_of_nonneg_right (by linarith) hm
      _ = K * m * t := by ring

/-- One cell: start `t0`, length `h`, input radius `δ`, defect bound `ε`, output radius `B`, box
`[UL, UH] × [VL, VH]`, the constants `L1`, `L2` of the Lipschitz bound, Lipschitz constant `K`
(of the field multiplied by t0), Taylor polynomials `pu`, `pv` in σ = t − t0. -/
structure Cell where
  t0 : ℚ
  h : ℚ
  δ : ℚ
  ε : ℚ
  B : ℚ
  UL : ℚ
  UH : ℚ
  VL : ℚ
  VH : ℚ
  L1 : ℚ
  L2 : ℚ
  K : ℚ
  pu : List ℚ
  pv : List ℚ

/-- (t0+σ) pu′ − pu (3 − pu − pv), computed. -/
def du1 (c : Cell) : List ℚ :=
  qsub (qmul [c.t0, 1] (qderiv c.pu)) (qmul c.pu (qsub (qsub [3] c.pu) c.pv))

/-- (t0+σ) pv′ − pv (pu − 1), computed. -/
def dv1 (c : Cell) : List ℚ :=
  qsub (qmul [c.t0, 1] (qderiv c.pv)) (qmul c.pv (qsub c.pu [1]))

/-- 2 pu − pv, computed. -/
def gp (c : Cell) : List ℚ := qsub (qsmul 2 c.pu) c.pv

/-- 6 pu − 2 pu² − 3 pu pv + pv, computed. -/
def Gp (c : Cell) : List ℚ :=
  qadd (qsub (qsub (qsmul 6 c.pu) (qsmul 2 (qmul c.pu c.pu))) (qsmul 3 (qmul c.pu c.pv))) c.pv

theorem du1_eval (c : Cell) (σ : ℝ) :
    ((c.t0 : ℝ) + σ) * dEvalQ c.pu σ - evalQ c.pu σ * (3 - evalQ c.pu σ - evalQ c.pv σ) =
      evalQ (du1 c) σ := by
  simp only [du1, evalQ_qsub, evalQ_qmul, ← dEvalQ_eq, evalQ]; push_cast; ring

theorem dv1_eval (c : Cell) (σ : ℝ) :
    ((c.t0 : ℝ) + σ) * dEvalQ c.pv σ - evalQ c.pv σ * (evalQ c.pu σ - 1) = evalQ (dv1 c) σ := by
  simp only [dv1, evalQ_qsub, evalQ_qmul, ← dEvalQ_eq, evalQ]; push_cast; ring

theorem gp_eval (c : Cell) (σ : ℝ) : 2 * evalQ c.pu σ - evalQ c.pv σ = evalQ (gp c) σ := by
  simp only [gp, evalQ_qsub, evalQ_qsmul]; push_cast; ring

theorem Gp_eval (c : Cell) (σ : ℝ) :
    6 * evalQ c.pu σ - 2 * evalQ c.pu σ ^ 2 - 3 * (evalQ c.pu σ * evalQ c.pv σ) + evalQ c.pv σ =
      evalQ (Gp c) σ := by
  simp only [Gp, evalQ_qadd, evalQ_qsub, evalQ_qsmul, evalQ_qmul]; push_cast; ring

/-- All side conditions of a cell (start `L` of the domain, end `T`) as one proposition over ℚ. -/
def CellProp (L T : ℚ) (c : Cell) : Prop :=
  L ≤ c.t0 ∧ 0 < c.t0 ∧ c.t0 + c.h ≤ T ∧ 0 < c.h ∧ 0 < c.UL ∧ 0 < c.VL ∧ 0 < c.K ∧
  c.K * c.h < 1 ∧ 0 ≤ c.δ ∧ 0 ≤ c.ε ∧
  3 - 2 * c.UL - c.VL ≤ c.L1 ∧ 2 * c.UH + c.VH - 3 ≤ c.L1 ∧ c.UH - 1 ≤ c.L2 ∧ 1 - c.UL ≤ c.L2 ∧
  c.L1 + c.UH ≤ c.K * c.t0 ∧ c.VH + c.L2 ≤ c.K * c.t0 ∧
  c.UL + 1 / 100 ≤ lo c.pu c.h ∧ hi c.pu c.h ≤ c.UH - 1 / 100 ∧
  c.VL + 1 / 100 ≤ lo c.pv c.h ∧ hi c.pv c.h ≤ c.VH - 1 / 100 ∧
  qabs (du1 c) c.h ≤ c.ε * c.t0 ∧ qabs (dv1 c) c.h ≤ c.ε * c.t0 ∧
  c.δ * (1 / (1 - c.K * c.h)) + c.ε / c.K * (1 / (1 - c.K * c.h) - 1) ≤ c.B ∧
  c.B < 1 / 100

instance (L T : ℚ) (c : Cell) : Decidable (CellProp L T c) := by
  unfold CellProp; infer_instance

/-- One validated cell from its Boolean check, for every solution (u, v) of the homology system with
derivatives within [L, T]. -/
theorem cell_q {L T : ℚ} (c : Cell) (hok : decide (CellProp L T c) = true) {u v : ℝ → ℝ}
    (hu : ∀ t ∈ Icc (c.t0 : ℝ) (c.t0 + c.h),
      HasDerivWithinAt u (u t * (3 - u t - v t) / t) (Icc (L : ℝ) T) t)
    (hv : ∀ t ∈ Icc (c.t0 : ℝ) (c.t0 + c.h),
      HasDerivWithinAt v (v t * (u t - 1) / t) (Icc (L : ℝ) T) t)
    (h0 : |u c.t0 - ((c.pu.headD 0 : ℚ) : ℝ)| ≤ c.δ)
    (h0' : |v c.t0 - ((c.pv.headD 0 : ℚ) : ℝ)| ≤ c.δ) :
    ∀ t ∈ Icc (c.t0 : ℝ) (c.t0 + c.h),
      |u t - evalQ c.pu (t - c.t0)| ≤ c.B ∧ |v t - evalQ c.pv (t - c.t0)| ≤ c.B := by
  obtain ⟨k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14, k15, k16, k17, k18, k19,
    k20, k21, k22, k23⟩ : CellProp L T c := of_decide_eq_true hok
  have r : ∀ {a b : ℚ}, a ≤ b → (a : ℝ) ≤ (b : ℝ) := fun h => by exact_mod_cast h
  have r0 := r k0
  have r10 := r k10; have r11 := r k11; have r12 := r k12; have r13 := r k13
  have r14 := r k14; have r15 := r k15; have r16 := r k16; have r17 := r k17
  have r18 := r k18; have r19 := r k19; have r20 := r k20; have r21 := r k21
  have r22 := r k22
  have r23 : ((c.B : ℚ) : ℝ) < ((1 / 100 : ℚ) : ℝ) := by exact_mod_cast k23
  push_cast at r0 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23
  have ht0 : (0 : ℝ) < c.t0 := by exact_mod_cast k1
  have hT : ((c.t0 : ℝ) + c.h) ≤ T := by exact_mod_cast k2
  have hh : (0 : ℝ) < c.h := by exact_mod_cast k3
  have hUL : (0 : ℝ) < c.UL := by exact_mod_cast k4
  have hVL : (0 : ℝ) < c.VL := by exact_mod_cast k5
  have hK : (0 : ℝ) < c.K := by exact_mod_cast k6
  have hKh : (c.K : ℝ) * c.h < 1 := by exact_mod_cast k7
  have hδ : (0 : ℝ) ≤ c.δ := by exact_mod_cast k8
  have hε : (0 : ℝ) ≤ c.ε := by exact_mod_cast k9
  have hT0 : Icc (c.t0 : ℝ) (c.t0 + c.h) ⊆ Icc (L : ℝ) T := Icc_subset_Icc r0 hT
  have hs : ∀ t ∈ Icc (c.t0 : ℝ) (c.t0 + c.h), t - c.t0 ∈ Icc (0 : ℝ) c.h := fun t ht =>
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  set f : ℝ → ℝ × ℝ := fun t => (u t, v t) with hfdef
  set g : ℝ → ℝ × ℝ := fun t => (evalQ c.pu (t - c.t0), evalQ c.pv (t - c.t0)) with hg
  have hfd : ∀ t ∈ Icc (c.t0 : ℝ) (c.t0 + c.h), HasDerivWithinAt f (hF t (f t)) (Icc (L : ℝ) T) t :=
    fun t ht => (hu t ht).prodMk (hv t ht)
  have key := tube_cell_t (F := hF) (K := Real.toNNReal c.K)
    (S := box c.UL c.UH c.VL c.VH) (f := f) (g := g)
    (g' := fun t => (dEvalQ c.pu (t - c.t0), dEvalQ c.pv (t - c.t0))) (a := c.t0) (b := c.t0 + c.h)
    (δ := c.δ) (ε := c.ε) (B := c.B) (B' := 1 / 100)
    (fun t ht => lip_box ht0 ht.1 hUL hVL r10 r11 r12 r13 r14 r15 hK.le) (by linarith)
    (fun t ht => ((hfd t ht).continuousWithinAt).mono hT0)
    (fun t ht => (hfd t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem ⟨by linarith [ht.1], by linarith [ht.2]⟩))
    (((continuous_evalQ c.pu).comp (continuous_sub_right _)).prodMk
      ((continuous_evalQ c.pv).comp (continuous_sub_right _))).continuousOn
    (fun t _ => (((hasDerivAt_evalQ c.pu (t - c.t0)).comp_sub_const t _).prodMk
      ((hasDerivAt_evalQ c.pv (t - c.t0)).comp_sub_const t _)).hasDerivWithinAt)
    (fun t ht => by
      have hσ := hs t (Ico_subset_Icc_self ht)
      have htpos : 0 < t := lt_of_lt_of_le ht0 ht.1
      have et : (c.t0 : ℝ) + (t - c.t0) = t := by ring
      simp only [hg, hF, Prod.dist_eq, Real.dist_eq]
      have hεt : (c.ε : ℝ) * c.t0 ≤ c.ε * t := mul_le_mul_of_nonneg_left ht.1 hε
      refine max_le ?_ ?_
      · have h1 := (abs_le_qabs (du1 c) hσ.1 hσ.2).trans r20
        rw [← du1_eval, et] at h1
        have e : dEvalQ c.pu (t - c.t0) -
            evalQ c.pu (t - c.t0) * (3 - evalQ c.pu (t - c.t0) - evalQ c.pv (t - c.t0)) / t =
            (t * dEvalQ c.pu (t - c.t0) -
              evalQ c.pu (t - c.t0) * (3 - evalQ c.pu (t - c.t0) - evalQ c.pv (t - c.t0))) / t := by
          field_simp
        rw [e, abs_div, abs_of_pos htpos, div_le_iff₀ htpos]
        linarith
      · have h1 := (abs_le_qabs (dv1 c) hσ.1 hσ.2).trans r21
        rw [← dv1_eval, et] at h1
        have e : dEvalQ c.pv (t - c.t0) - evalQ c.pv (t - c.t0) * (evalQ c.pu (t - c.t0) - 1) / t =
            (t * dEvalQ c.pv (t - c.t0) - evalQ c.pv (t - c.t0) * (evalQ c.pu (t - c.t0) - 1)) / t := by
          field_simp
        rw [e, abs_div, abs_of_pos htpos, div_le_iff₀ htpos]
        linarith)
    (fun t ht z hz => by
      simp only [hg, Prod.dist_eq, Real.dist_eq, max_lt_iff] at hz
      have g1 := lo_le c.pu (hs t ht).1 (hs t ht).2
      have g2 := le_hi c.pu (hs t ht).1 (hs t ht).2
      have g3 := lo_le c.pv (hs t ht).1 (hs t ht).2
      have g4 := le_hi c.pv (hs t ht).1 (hs t ht).2
      have a1 := abs_lt.1 hz.1
      have a2 := abs_lt.1 hz.2
      show (c.UL : ℝ) ≤ z.1 ∧ z.1 ≤ c.UH ∧ (c.VL : ℝ) ≤ z.2 ∧ z.2 ≤ c.VH
      refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith [a1.1, a1.2, a2.1, a2.2])
    r23
    (by
      simp only [hfdef, hg, sub_self, Prod.dist_eq, Real.dist_eq]
      rw [evalQ_zero_head, evalQ_zero_head]
      exact max_le h0 h0')
    (fun t ht => by
      rw [Real.coe_toNNReal _ hK.le]
      exact (gronwallBound_le_cell hδ hε hK (show t - c.t0 ≤ c.h by linarith [ht.2]) hh hKh).trans r22)
  intro t ht
  have h1 := key t ht
  simp only [hfdef, hg, Prod.dist_eq, Real.dist_eq] at h1
  exact ⟨(le_max_left _ _).trans h1, (le_max_right _ _).trans h1⟩

/-- The invariant of a cell as a proposition over ℚ: 1 = (2u − v > 0), 2 = (2u − v < 0),
3 = (6u − 2u² − 3uv + v > 0), otherwise none. -/
def InvProp (m : ℕ) (c : Cell) : Prop :=
  match m with
  | 1 => 0 < lo (gp c) c.h - 3 * c.B
  | 2 => hi (gp c) c.h + 3 * c.B < 0
  | 3 => 0 < lo (Gp c) c.h - (7 + 7 * c.UH + 3 * c.VH) * c.B
  | _ => True

instance (m : ℕ) (c : Cell) : Decidable (InvProp m c) := by
  unfold InvProp; split <;> infer_instance

/-- The invariant as a statement about the solution at radius t. -/
def Inv (m : ℕ) (u v : ℝ → ℝ) (t : ℝ) : Prop :=
  match m with
  | 1 => 0 < 2 * u t - v t
  | 2 => 2 * u t - v t < 0
  | 3 => 0 < 6 * u t - 2 * u t ^ 2 - 3 * (u t * v t) + v t
  | _ => True

/-- Cell conditions and invariant, as a Boolean for evaluation by the kernel. -/
def cellOK (L T : ℚ) (m : ℕ) (c : Cell) : Bool := decide (CellProp L T c) && decide (InvProp m c)

theorem cell_basic {L T : ℚ} {m : ℕ} (c : Cell) (hok : cellOK L T m c = true) :
    L ≤ c.t0 ∧ 0 < c.t0 ∧ c.t0 + c.h ≤ T ∧ 0 < c.h := by
  simp only [cellOK, Bool.and_eq_true] at hok
  obtain ⟨k0, k1, k2, k3, -⟩ : CellProp L T c := of_decide_eq_true hok.1
  exact ⟨k0, k1, k2, k3⟩

/-- The box of a cell holds the solution, and the solution's values on the cell. -/
theorem cell_box {L T : ℚ} (c : Cell) (hok : decide (CellProp L T c) = true) {u v : ℝ → ℝ} {t : ℝ}
    (ht : t ∈ Icc (c.t0 : ℝ) (c.t0 + c.h))
    (e1 : |u t - evalQ c.pu (t - c.t0)| ≤ c.B) (e2 : |v t - evalQ c.pv (t - c.t0)| ≤ c.B) :
    (c.UL : ℝ) ≤ u t ∧ u t ≤ c.UH ∧ (c.VL : ℝ) ≤ v t ∧ v t ≤ c.VH ∧
    (c.UL : ℝ) ≤ evalQ c.pu (t - c.t0) ∧ evalQ c.pu (t - c.t0) ≤ c.UH ∧
    (c.VL : ℝ) ≤ evalQ c.pv (t - c.t0) ∧ evalQ c.pv (t - c.t0) ≤ c.VH ∧ (0 : ℝ) ≤ c.B ∧
    (0 : ℝ) < c.UL ∧ (0 : ℝ) < c.VL := by
  obtain ⟨-, -, -, -, k4, k5, -, -, -, -, -, -, -, -, -, -, k16, k17, k18, k19, -, -, -, k23⟩ :
    CellProp L T c := of_decide_eq_true hok
  have r : ∀ {a b : ℚ}, a ≤ b → (a : ℝ) ≤ (b : ℝ) := fun h => by exact_mod_cast h
  have r16 := r k16; have r17 := r k17; have r18 := r k18; have r19 := r k19
  have r23 : ((c.B : ℚ) : ℝ) < ((1 / 100 : ℚ) : ℝ) := by exact_mod_cast k23
  push_cast at r16 r17 r18 r19 r23
  have hσ0 : 0 ≤ t - c.t0 := by linarith [ht.1]
  have hσ1 : t - c.t0 ≤ c.h := by linarith [ht.2]
  have g1 := lo_le c.pu hσ0 hσ1
  have g2 := le_hi c.pu hσ0 hσ1
  have g3 := lo_le c.pv hσ0 hσ1
  have g4 := le_hi c.pv hσ0 hσ1
  have a1 := abs_le.1 e1
  have a2 := abs_le.1 e2
  have hB : (0 : ℝ) ≤ c.B := (abs_nonneg _).trans e1
  have r4 : (0 : ℝ) < c.UL := by exact_mod_cast k4
  have r5 : (0 : ℝ) < c.VL := by exact_mod_cast k5
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hB, r4, r5⟩ <;> linarith

/-- What one cell gives: the invariant on the cell and the end enclosure. -/
theorem cell_facts {L T : ℚ} {m : ℕ} (c : Cell) (hok : cellOK L T m c = true) {u v : ℝ → ℝ}
    (hu : ∀ t ∈ Icc (c.t0 : ℝ) (c.t0 + c.h),
      HasDerivWithinAt u (u t * (3 - u t - v t) / t) (Icc (L : ℝ) T) t)
    (hv : ∀ t ∈ Icc (c.t0 : ℝ) (c.t0 + c.h),
      HasDerivWithinAt v (v t * (u t - 1) / t) (Icc (L : ℝ) T) t)
    (h0 : |u c.t0 - ((c.pu.headD 0 : ℚ) : ℝ)| ≤ c.δ)
    (h0' : |v c.t0 - ((c.pv.headD 0 : ℚ) : ℝ)| ≤ c.δ) :
    (∀ t ∈ Icc (c.t0 : ℝ) (c.t0 + c.h), Inv m u v t) ∧
    |u (c.t0 + c.h) - ((qeval c.pu c.h : ℚ) : ℝ)| ≤ c.B ∧
    |v (c.t0 + c.h) - ((qeval c.pv c.h : ℚ) : ℝ)| ≤ c.B := by
  have hok' := hok
  simp only [cellOK, Bool.and_eq_true] at hok'
  have hc := cell_q c hok'.1 hu hv h0 h0'
  obtain ⟨-, -, -, k3⟩ := cell_basic c hok
  have hh : (0 : ℝ) < c.h := by exact_mod_cast k3
  refine ⟨fun t ht => ?_, ?_, ?_⟩
  · have hσ0 : 0 ≤ t - c.t0 := by linarith [ht.1]
    have hσ1 : t - c.t0 ≤ c.h := by linarith [ht.2]
    obtain ⟨e1, e2⟩ := hc t ht
    obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, hB, hUL, hVL⟩ := cell_box c hok'.1 ht e1 e2
    have a1 := abs_le.1 e1
    have a2 := abs_le.1 e2
    have kv := of_decide_eq_true hok'.2
    match m, kv with
    | 1, kv =>
      have rv : ((0 : ℚ) : ℝ) < ((lo (gp c) c.h - 3 * c.B : ℚ) : ℝ) := by exact_mod_cast kv
      push_cast at rv
      have hl := lo_le (gp c) hσ0 hσ1
      rw [← gp_eval] at hl
      show 0 < 2 * u t - v t
      linarith
    | 2, kv =>
      have rv : ((hi (gp c) c.h + 3 * c.B : ℚ) : ℝ) < ((0 : ℚ) : ℝ) := by exact_mod_cast kv
      push_cast at rv
      have hl := le_hi (gp c) hσ0 hσ1
      rw [← gp_eval] at hl
      show 2 * u t - v t < 0
      linarith
    | 3, kv =>
      have rv : ((0 : ℚ) : ℝ) < ((lo (Gp c) c.h - (7 + 7 * c.UH + 3 * c.VH) * c.B : ℚ) : ℝ) := by
        exact_mod_cast kv
      push_cast at rv
      have hl := lo_le (Gp c) hσ0 hσ1
      rw [← Gp_eval] at hl
      show 0 < 6 * u t - 2 * u t ^ 2 - 3 * (u t * v t) + v t
      set p := evalQ c.pu (t - c.t0)
      set q := evalQ c.pv (t - c.t0)
      have e : (6 * u t - 2 * u t ^ 2 - 3 * (u t * v t) + v t) -
          (6 * p - 2 * p ^ 2 - 3 * (p * q) + q) =
          (6 - 2 * (u t + p) - 3 * v t) * (u t - p) + (1 - 3 * p) * (v t - q) := by ring
      have c1 : |6 - 2 * (u t + p) - 3 * v t| ≤ 6 + 4 * c.UH + 3 * c.VH := by
        rw [abs_le]; constructor <;> linarith
      have c2 : |1 - 3 * p| ≤ 1 + 3 * c.UH := by rw [abs_le]; constructor <;> linarith
      have d : |(6 - 2 * (u t + p) - 3 * v t) * (u t - p) + (1 - 3 * p) * (v t - q)| ≤
          (7 + 7 * c.UH + 3 * c.VH) * c.B := by
        calc _ ≤ |(6 - 2 * (u t + p) - 3 * v t) * (u t - p)| + |(1 - 3 * p) * (v t - q)| :=
              abs_add_le _ _
          _ = |6 - 2 * (u t + p) - 3 * v t| * |u t - p| + |1 - 3 * p| * |v t - q| := by
              rw [abs_mul, abs_mul]
          _ ≤ (6 + 4 * c.UH + 3 * c.VH) * c.B + (1 + 3 * c.UH) * c.B := by
              gcongr <;> linarith [abs_nonneg (6 - 2 * (u t + p) - 3 * v t), abs_nonneg (1 - 3 * p)]
          _ = (7 + 7 * c.UH + 3 * c.VH) * c.B := by ring
      rw [← e] at d
      have := (abs_le.1 d).1
      linarith
    | 0, _ => trivial
    | (n + 4), _ => trivial
  · have e := (hc (c.t0 + c.h) ⟨by linarith, le_rfl⟩).1
    rwa [add_sub_cancel_left, ← qeval_cast] at e
  · have e := (hc (c.t0 + c.h) ⟨by linarith, le_rfl⟩).2
    rwa [add_sub_cancel_left, ← qeval_cast] at e

/-- Consecutive cells meet, and the end enclosure of `c` lies in the input box of `d`. -/
def linkOK (c d : Cell) : Bool :=
  decide (c.t0 + c.h = d.t0 ∧
    |qeval c.pu c.h - d.pu.headD 0| + c.B ≤ d.δ ∧
    |qeval c.pv c.h - d.pv.headD 0| + c.B ≤ d.δ)

/-- A chain of cells inside [L, T] with invariant `m`, whose last cell satisfies `term`. -/
def chainTo (L T : ℚ) (m : ℕ) (term : Cell → Bool) : List Cell → Bool
  | [] => false
  | [c] => cellOK L T m c && term c
  | c :: d :: l => cellOK L T m c && linkOK c d && chainTo L T m term (d :: l)

/-- Terminal condition: the last cell ends at `te` with its enclosure within `r` of (fu, fv). -/
def endOK (te fu fv r : ℚ) (c : Cell) : Bool :=
  decide (c.t0 + c.h = te ∧ |qeval c.pu c.h - fu| + c.B ≤ r ∧ |qeval c.pv c.h - fv| + c.B ≤ r)

theorem chain_gen {L T : ℚ} {m : ℕ} {term : Cell → Bool} {u v : ℝ → ℝ} :
    ∀ (l : List Cell) (c : Cell), chainTo L T m term (c :: l) = true →
    (∀ t ∈ Icc (c.t0 : ℝ) T, HasDerivWithinAt u (u t * (3 - u t - v t) / t) (Icc (L : ℝ) T) t) →
    (∀ t ∈ Icc (c.t0 : ℝ) T, HasDerivWithinAt v (v t * (u t - 1) / t) (Icc (L : ℝ) T) t) →
    |u c.t0 - ((c.pu.headD 0 : ℚ) : ℝ)| ≤ c.δ →
    |v c.t0 - ((c.pv.headD 0 : ℚ) : ℝ)| ≤ c.δ →
    ∃ e : Cell, term e = true ∧ (c.t0 : ℝ) ≤ e.t0 + e.h ∧
    (∀ t ∈ Icc (c.t0 : ℝ) (e.t0 + e.h), Inv m u v t) ∧
    |u (e.t0 + e.h) - ((qeval e.pu e.h : ℚ) : ℝ)| ≤ e.B ∧
    |v (e.t0 + e.h) - ((qeval e.pv e.h : ℚ) : ℝ)| ≤ e.B := by
  intro l
  induction l with
  | nil =>
    intro c hok hu hv h0 h0'
    simp only [chainTo, Bool.and_eq_true] at hok
    obtain ⟨k1, kt⟩ := hok
    obtain ⟨-, -, k2, k3⟩ := cell_basic c k1
    have k2' : ((c.t0 + c.h : ℚ) : ℝ) ≤ T := by exact_mod_cast k2
    have hh : (0 : ℝ) < c.h := by exact_mod_cast k3
    push_cast at k2'
    have hf := cell_facts c k1 (u := u) (v := v)
      (fun t ht => hu t ⟨ht.1, by linarith [ht.2]⟩)
      (fun t ht => hv t ⟨ht.1, by linarith [ht.2]⟩) h0 h0'
    exact ⟨c, kt, by linarith, hf⟩
  | cons d l ih =>
    intro c hok hu hv h0 h0'
    simp only [chainTo, Bool.and_eq_true] at hok
    obtain ⟨⟨k1, kl⟩, krest⟩ := hok
    obtain ⟨ke, kE, kφ⟩ := of_decide_eq_true kl
    have he : ((c.t0 + c.h : ℚ) : ℝ) = (d.t0 : ℝ) := by exact_mod_cast ke
    push_cast at he
    obtain ⟨-, -, k2, k3⟩ := cell_basic c k1
    have hh : (0 : ℝ) < c.h := by exact_mod_cast k3
    have k2' : ((c.t0 + c.h : ℚ) : ℝ) ≤ T := by exact_mod_cast k2
    push_cast at k2'
    have hf := cell_facts c k1 (u := u) (v := v)
      (fun t ht => hu t ⟨ht.1, by linarith [ht.2]⟩)
      (fun t ht => hv t ⟨ht.1, by linarith [ht.2]⟩) h0 h0'
    rw [he] at hf
    have kE' : |((qeval c.pu c.h : ℚ) : ℝ) - ((d.pu.headD 0 : ℚ) : ℝ)| + c.B ≤ d.δ := by
      exact_mod_cast kE
    have kφ' : |((qeval c.pv c.h : ℚ) : ℝ) - ((d.pv.headD 0 : ℚ) : ℝ)| + c.B ≤ d.δ := by
      exact_mod_cast kφ
    obtain ⟨e, het, hce, hinv, hb1, hb2⟩ := ih d krest
      (fun t ht => hu t ⟨by linarith [ht.1], ht.2⟩)
      (fun t ht => hv t ⟨by linarith [ht.1], ht.2⟩)
      (abs_link hf.2.1 kE') (abs_link hf.2.2 kφ')
    exact ⟨e, het, by linarith, icc_glue hf.1 hinv, hb1, hb2⟩

/-- A segment of a chain: the invariant up to the start of `d`, and the solution enters the input
box of `d`. -/
theorem seg_q {L T : ℚ} {m : ℕ} {u v : ℝ → ℝ} (d : Cell) (l : List Cell) (c : Cell)
    (hok : chainTo L T m (fun e => linkOK e d) (c :: l) = true)
    (hu : ∀ t ∈ Icc (c.t0 : ℝ) T, HasDerivWithinAt u (u t * (3 - u t - v t) / t) (Icc (L : ℝ) T) t)
    (hv : ∀ t ∈ Icc (c.t0 : ℝ) T, HasDerivWithinAt v (v t * (u t - 1) / t) (Icc (L : ℝ) T) t)
    (h0 : |u c.t0 - ((c.pu.headD 0 : ℚ) : ℝ)| ≤ c.δ)
    (h0' : |v c.t0 - ((c.pv.headD 0 : ℚ) : ℝ)| ≤ c.δ) :
    (c.t0 : ℝ) ≤ d.t0 ∧ (∀ t ∈ Icc (c.t0 : ℝ) d.t0, Inv m u v t) ∧
    |u d.t0 - ((d.pu.headD 0 : ℚ) : ℝ)| ≤ d.δ ∧ |v d.t0 - ((d.pv.headD 0 : ℚ) : ℝ)| ≤ d.δ := by
  obtain ⟨e, het, hce, hinv, hb1, hb2⟩ := chain_gen l c hok hu hv h0 h0'
  obtain ⟨ke, kE, kφ⟩ := of_decide_eq_true het
  have he : ((e.t0 + e.h : ℚ) : ℝ) = (d.t0 : ℝ) := by exact_mod_cast ke
  push_cast at he
  rw [he] at hce hinv hb1 hb2
  have kE' : |((qeval e.pu e.h : ℚ) : ℝ) - ((d.pu.headD 0 : ℚ) : ℝ)| + e.B ≤ d.δ := by
    exact_mod_cast kE
  have kφ' : |((qeval e.pv e.h : ℚ) : ℝ) - ((d.pv.headD 0 : ℚ) : ℝ)| + e.B ≤ d.δ := by
    exact_mod_cast kφ
  exact ⟨hce, hinv, abs_link hb1 kE', abs_link hb2 kφ'⟩

/-- The last segment of a chain: the invariant up to `te`, and the solution is within `r` of
(fu, fv) at `te`. -/
theorem end_q {L T te fu fv r : ℚ} {m : ℕ} {u v : ℝ → ℝ} (l : List Cell) (c : Cell)
    (hok : chainTo L T m (endOK te fu fv r) (c :: l) = true)
    (hu : ∀ t ∈ Icc (c.t0 : ℝ) T, HasDerivWithinAt u (u t * (3 - u t - v t) / t) (Icc (L : ℝ) T) t)
    (hv : ∀ t ∈ Icc (c.t0 : ℝ) T, HasDerivWithinAt v (v t * (u t - 1) / t) (Icc (L : ℝ) T) t)
    (h0 : |u c.t0 - ((c.pu.headD 0 : ℚ) : ℝ)| ≤ c.δ)
    (h0' : |v c.t0 - ((c.pv.headD 0 : ℚ) : ℝ)| ≤ c.δ) :
    (∀ t ∈ Icc (c.t0 : ℝ) te, Inv m u v t) ∧ |u te - fu| ≤ r ∧ |v te - fv| ≤ r := by
  obtain ⟨e, het, -, hinv, hb1, hb2⟩ := chain_gen l c hok hu hv h0 h0'
  obtain ⟨ke, kE, kφ⟩ := of_decide_eq_true het
  have he : ((e.t0 + e.h : ℚ) : ℝ) = (te : ℝ) := by exact_mod_cast ke
  push_cast at he
  rw [he] at hinv hb1 hb2
  have kE' : |((qeval e.pu e.h : ℚ) : ℝ) - fu| + e.B ≤ r := by exact_mod_cast kE
  have kφ' : |((qeval e.pv e.h : ℚ) : ℝ) - fv| + e.B ≤ r := by exact_mod_cast kφ
  exact ⟨hinv, abs_link hb1 kE', abs_link hb2 kφ'⟩

end Work.Math.BEHCell
