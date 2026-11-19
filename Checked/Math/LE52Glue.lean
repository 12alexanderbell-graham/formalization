import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Checked.Sim.ODETools
import Checked.Sim.QPoly
import Checked.Math.LEGStart
import Checked.Math.LE52CellQ

/-! Lane–Emden equation of index five halves: the singular start (`start52`, the generic start of `Checked.Math.LEGStart` with a residual certified through the square-root polynomial) and the last cell (`last52`: sign change of θ, φ negative, bounds on the mass factor), each from one proposition over the rationals decided by kernel evaluation; `qeqB` compares coefficient lists with order relations only. Promoted verbatim from `Work/Math/LE52Glue.lean`. -/

namespace Checked.Math.LE52Glue
open Set Checked.Sim Checked.Sim.QPoly Checked.Math.LENCell Checked.Math.LE52Cell Checked.Math.LE52CellQ

/-- All coefficients zero, as a Boolean built from `≤` (kernel-evaluable). -/
def qzeroB : List ℚ → Bool
  | [] => true
  | a :: p => decide (a ≤ 0) && decide (0 ≤ a) && qzeroB p

theorem qzeroB_eval : ∀ p : List ℚ, qzeroB p = true → ∀ s : ℝ, evalQ p s = 0
  | [], _, _ => rfl
  | a :: p, h, s => by
    simp only [qzeroB, Bool.and_eq_true, decide_eq_true_eq] at h
    have ha : a = 0 := le_antisymm h.1.1 h.1.2
    simp only [evalQ]
    rw [ha, qzeroB_eval p h.2 s]; simp

/-- Equality of rational polynomials (trailing zeros ignored) as a Boolean built from `≤`
(kernel-evaluable; structural recursion on the first list). -/
def qeqB : List ℚ → List ℚ → Bool
  | [], q => qzeroB q
  | a :: p, [] => decide (a ≤ 0) && decide (0 ≤ a) && qzeroB p
  | a :: p, b :: q => decide (a ≤ b) && decide (b ≤ a) && qeqB p q

theorem qeqB_eval : ∀ p q : List ℚ, qeqB p q = true → ∀ s : ℝ, evalQ p s = evalQ q s
  | [], q, h, s => by
    rw [qzeroB_eval q h s]; rfl
  | a :: p, [], h, s => by
    simp only [qeqB, Bool.and_eq_true, decide_eq_true_eq] at h
    have ha : a = 0 := le_antisymm h.1.1 h.1.2
    simp only [evalQ]
    rw [ha, qzeroB_eval p h.2 s]; simp
  | a :: p, b :: q, h, s => by
    simp only [qeqB, Bool.and_eq_true, decide_eq_true_eq] at h
    have hab : a = b := le_antisymm h.1.1 h.1.2
    simp only [evalQ]
    rw [hab, qeqB_eval p q h.2 s]

/-- The rational side conditions of the singular start. -/
structure StartData where
  P : List ℚ
  Pw : List ℚ
  W2 : List ℚ
  Pdt : List ℚ
  ξ0 : ℚ
  η : ℚ
  R : ℚ
  L : ℚ
  Mp : ℚ
  S : ℚ
  c0 : ℚ
  P0 : ℚ
  η0 : ℚ
  γ0 : ℚ
  Rp : ℚ

def StartProp (d : StartData) : Prop :=
  1 ≤ d.P.headD 0 ∧ d.P.headD 0 ≤ 1 ∧
  qeqB (qderiv (qmul [0, 0, 1] (qderiv d.P))) (0 :: 0 :: d.W2) = true ∧
  qeqB (qderiv d.P) (0 :: d.Pdt) = true ∧
  qabs (qadd d.W2 (qquint d.Pw)) d.ξ0 ≤ d.Rp ∧
  0 < d.c0 ∧ d.c0 ≤ d.Pw.headD 0 - d.ξ0 * qabs d.Pw.tail d.ξ0 ∧
  d.Pw.headD 0 + d.ξ0 * qabs d.Pw.tail d.ξ0 ≤ d.P0 ∧
  qabs (qsub (qmul d.Pw d.Pw) d.P) d.ξ0 ≤ d.η0 ∧ d.η0 < d.c0 ^ 2 ∧
  d.η0 / d.c0 * (5 * (d.P0 ^ 2 + d.η0) ^ 2) ≤ d.γ0 ∧ d.Rp + d.γ0 ≤ d.R ∧ 0 ≤ d.R ∧
  qabs d.P d.ξ0 ≤ d.Mp ∧ 0 ≤ d.S ∧ d.Mp + d.η ≤ d.S ^ 2 ∧ 5 / 2 * d.S ^ 3 ≤ d.L ∧ 0 < d.η ∧
  0 < d.ξ0 ∧ d.ξ0 ^ 2 / 6 * (d.L * d.η + d.R) < d.η ∧
  d.Pdt.headD 0 + d.ξ0 * qabs d.Pdt.tail d.ξ0 + (d.L * d.η + d.R) / 3 < 0

instance (d : StartData) : Decidable (StartProp d) := by unfold StartProp; infer_instance

def startOK (d : StartData) : Bool := decide (StartProp d)

theorem evalQ_x2 (s : ℝ) : evalQ [0, 0, 1] s = s ^ 2 := by simp [evalQ]; ring

/-- The singular start from its Boolean check. -/
theorem start52 (d : StartData) (hok : startOK d = true) {X : ℝ} (hX : (d.ξ0 : ℝ) ≤ X)
    {θ φ : ℝ → ℝ}
    (hθ : ∀ ξ ∈ Icc (0 : ℝ) X, HasDerivWithinAt θ (φ ξ) (Icc 0 X) ξ)
    (hφ0 : ContinuousWithinAt φ (Icc 0 X) 0)
    (hφ : ∀ ξ ∈ Ioc (0 : ℝ) X, HasDerivWithinAt φ (-(2 / ξ * φ ξ) - g52 (θ ξ)) (Icc 0 X) ξ)
    (h0 : θ 0 = 1) :
    (∀ t ∈ Ioc (0 : ℝ) d.ξ0, φ t < 0) ∧
    |θ d.ξ0 - ((qeval d.P d.ξ0 : ℚ) : ℝ)| ≤ (d.ξ0 : ℝ) ^ 2 / 6 * (d.L * d.η + d.R) ∧
    |φ d.ξ0 - ((qeval (qderiv d.P) d.ξ0 : ℚ) : ℝ)| ≤ (d.ξ0 : ℝ) / 3 * (d.L * d.η + d.R) := by
  obtain ⟨k1a, k1b, k2q, k2q', k3, k4, k5, k6, k7, k8, k9, k10, k11, k11', k12, k13, k14, k15, k16, k17,
    k18⟩ := of_decide_eq_true hok
  have k1 : d.P.headD 0 = 1 := le_antisymm k1b k1a
  have k2 := qeqB_eval _ _ k2q
  have k2' := qeqB_eval _ _ k2q'
  -- real forms
  have r3 : ((qabs (qadd d.W2 (qquint d.Pw)) d.ξ0 : ℚ) : ℝ) ≤ d.Rp := by exact_mod_cast k3
  have r4 : (0 : ℝ) < d.c0 := by exact_mod_cast k4
  have r5 : (d.c0 : ℝ) ≤ ((d.Pw.headD 0 - d.ξ0 * qabs d.Pw.tail d.ξ0 : ℚ) : ℝ) := by
    exact_mod_cast k5
  have r6 : ((d.Pw.headD 0 + d.ξ0 * qabs d.Pw.tail d.ξ0 : ℚ) : ℝ) ≤ d.P0 := by exact_mod_cast k6
  have r7 : ((qabs (qsub (qmul d.Pw d.Pw) d.P) d.ξ0 : ℚ) : ℝ) ≤ d.η0 := by exact_mod_cast k7
  have r8 : ((d.η0 : ℚ) : ℝ) < ((d.c0 ^ 2 : ℚ) : ℝ) := by exact_mod_cast k8
  have r9 : ((d.η0 / d.c0 * (5 * (d.P0 ^ 2 + d.η0) ^ 2) : ℚ) : ℝ) ≤ d.γ0 := by exact_mod_cast k9
  have r10 : ((d.Rp + d.γ0 : ℚ) : ℝ) ≤ d.R := by exact_mod_cast k10
  have r11 : (0 : ℝ) ≤ d.R := by exact_mod_cast k11
  have r12 : ((qabs d.P d.ξ0 : ℚ) : ℝ) ≤ d.Mp := by exact_mod_cast k11'
  have r13 : (0 : ℝ) ≤ d.S := by exact_mod_cast k12
  have r14 : ((d.Mp + d.η : ℚ) : ℝ) ≤ ((d.S ^ 2 : ℚ) : ℝ) := by exact_mod_cast k13
  have r15 : ((5 / 2 * d.S ^ 3 : ℚ) : ℝ) ≤ d.L := by exact_mod_cast k14
  have r16 : (0 : ℝ) < d.η := by exact_mod_cast k15
  have r17 : (0 : ℝ) < d.ξ0 := by exact_mod_cast k16
  have r18 : ((d.ξ0 ^ 2 / 6 * (d.L * d.η + d.R) : ℚ) : ℝ) < d.η := by exact_mod_cast k17
  have r19 : ((d.Pdt.headD 0 + d.ξ0 * qabs d.Pdt.tail d.ξ0 + (d.L * d.η + d.R) / 3 : ℚ) : ℝ) <
      ((0 : ℚ) : ℝ) := by exact_mod_cast k18
  push_cast at r8 r9 r10 r14 r15 r18 r19
  have hL0 : (0 : ℝ) ≤ d.L := by nlinarith [pow_nonneg r13 3]
  -- the reference, its derivative and the residual
  have hp : ∀ ξ, HasDerivAt (evalQ d.P) (evalQ (qderiv d.P) ξ) ξ := fun ξ => by
    rw [← dEvalQ_eq]; exact hasDerivAt_evalQ d.P ξ
  have hp0 : evalQ d.P 0 = 1 := by
    rw [evalQ_zero_head, k1]; norm_num
  have hq : ∀ ξ, HasDerivAt (fun t => t ^ 2 * evalQ (qderiv d.P) t)
      (evalQ (0 :: 0 :: d.W2) ξ) ξ := fun ξ => by
    have e : (fun t => t ^ 2 * evalQ (qderiv d.P) t) = evalQ (qmul [0, 0, 1] (qderiv d.P)) := by
      funext t; rw [evalQ_qmul, evalQ_x2]
    rw [e, ← k2 ξ, ← dEvalQ_eq]; exact hasDerivAt_evalQ _ ξ
  have hres : ∀ ξ ∈ Icc (0 : ℝ) d.ξ0,
      |evalQ (0 :: 0 :: d.W2) ξ + ξ ^ 2 * g52 (evalQ d.P ξ)| ≤ ξ ^ 2 * d.R := by
    intro ξ hξ
    rw [evalQ_cons0, evalQ_cons0]
    have e : ξ * (ξ * evalQ d.W2 ξ) + ξ ^ 2 * g52 (evalQ d.P ξ) =
        ξ ^ 2 * ((evalQ d.W2 ξ + evalQ d.Pw ξ ^ 5) + (g52 (evalQ d.P ξ) - evalQ d.Pw ξ ^ 5)) := by
      ring
    rw [e, abs_mul, abs_of_nonneg (sq_nonneg ξ)]
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg ξ)
    have a1 : |evalQ d.W2 ξ + evalQ d.Pw ξ ^ 5| ≤ d.Rp := by
      have := abs_le_qabs (qadd d.W2 (qquint d.Pw)) hξ.1 hξ.2
      rw [evalQ_qadd, evalQ_qquint] at this
      exact this.trans r3
    have hsq : |evalQ d.Pw ξ ^ 2 - evalQ d.P ξ| ≤ d.η0 := by
      have := abs_le_qabs (qsub (qmul d.Pw d.Pw) d.P) hξ.1 hξ.2
      rw [evalQ_qsub, evalQ_qmul] at this
      rw [sq]; exact this.trans r7
    have a2 := g52_close r4 (r5.trans (lower_q d.Pw hξ.1 hξ.2))
      ((upper_q d.Pw hξ.1 hξ.2).trans r6) hsq r8
    calc _ ≤ |evalQ d.W2 ξ + evalQ d.Pw ξ ^ 5| + |g52 (evalQ d.P ξ) - evalQ d.Pw ξ ^ 5| :=
          abs_add_le _ _
      _ ≤ d.Rp + d.γ0 := add_le_add a1 (a2.trans r9)
      _ ≤ d.R := r10
  have hpM : ∀ ξ ∈ Icc (0 : ℝ) d.ξ0, |evalQ d.P ξ| ≤ d.Mp := fun ξ hξ =>
    (abs_le_qabs d.P hξ.1 hξ.2).trans r12
  have hG : ∀ a b : ℝ, |a - b| ≤ (d.η : ℝ) → |b| ≤ (d.Mp : ℝ) →
      |g52 a - g52 b| ≤ (d.L : ℝ) * |a - b| := by
    intro a b hab hb
    have ha : |a| ≤ ((d.Mp : ℝ) + d.η) := by
      calc |a| = |(a - b) + b| := by rw [sub_add_cancel]
        _ ≤ |a - b| + |b| := abs_add_le _ _
        _ ≤ (d.Mp : ℝ) + d.η := by linarith
    have hb' : |b| ≤ (d.Mp : ℝ) + d.η := by linarith
    exact (g52_lip ha hb' r13 r14).trans
      (mul_le_mul_of_nonneg_right r15 (abs_nonneg _))
  have hs := Checked.Math.LEGStart.start g52 θ φ (evalQ d.P) (evalQ (qderiv d.P))
    (evalQ (0 :: 0 :: d.W2)) (X := X) (ξ0 := d.ξ0) (η := d.η) (R := d.R) (L := d.L) (Mp := d.Mp)
    r17 hX hθ hφ0 hφ h0 hp hp0 hq hres hpM hG hL0 r16 r11 r18
  refine ⟨fun t ht => ?_, ?_, ?_⟩
  · have h1 := (hs t ⟨ht.1.le, ht.2⟩).2
    rw [k2' t, evalQ_cons0, abs_le] at h1
    have hu := upper_q d.Pdt ht.1.le ht.2
    push_cast at hu
    have h3 : evalQ d.Pdt t + (d.L * d.η + d.R) / 3 < 0 := by linarith
    have h4 : t * (evalQ d.Pdt t + (d.L * d.η + d.R) / 3) < 0 := mul_neg_of_pos_of_neg ht.1 h3
    nlinarith [h1.2]
  · rw [qeval_cast]; exact (hs d.ξ0 ⟨r17.le, le_rfl⟩).1
  · rw [qeval_cast]; exact (hs d.ξ0 ⟨r17.le, le_rfl⟩).2

/-- The polynomial ξ² φ on the last cell, in σ = ξ − t0. -/
def ucube (c : Cell) : List ℚ := qmul (qmul [c.t0, 1] [c.t0, 1]) c.pp

/-- What the last cell must show: θ > 0 at its start, θ < 0 at its end, φ < 0 on it, and bounds
on −ξ² φ. -/
def LastProp (c : Cell) (wlo whi : ℚ) : Prop :=
  0 < c.pt.headD 0 - c.δ ∧ qeval c.pt c.h + c.B < 0 ∧
  c.pp.headD 0 + c.h * qabs c.pp.tail c.h + c.B < 0 ∧
  wlo ≤ -((ucube c).headD 0 + c.h * qabs (ucube c).tail c.h) - (c.t0 + c.h) ^ 2 * c.B ∧
  -((ucube c).headD 0 - c.h * qabs (ucube c).tail c.h) + (c.t0 + c.h) ^ 2 * c.B ≤ whi

instance (c : Cell) (wlo whi : ℚ) : Decidable (LastProp c wlo whi) := by
  unfold LastProp; infer_instance

def lastOK (c : Cell) (wlo whi : ℚ) : Bool := decide (LastProp c wlo whi)

/-- The last cell from its Boolean checks. -/
theorem last52 {T : ℚ} (c : Cell) (wlo whi : ℚ) (hok : cellOK T c = true)
    (hl : lastOK c wlo whi = true) {θ φ : ℝ → ℝ}
    (hθ : ∀ t ∈ Icc (c.t0 : ℝ) (c.t0 + c.h), HasDerivWithinAt θ (φ t) (Icc 0 (T : ℝ)) t)
    (hφ : ∀ t ∈ Icc (c.t0 : ℝ) (c.t0 + c.h),
      HasDerivWithinAt φ (-(2 / t * φ t) - g52 (θ t)) (Icc 0 (T : ℝ)) t)
    (h0 : |θ c.t0 - ((c.pt.headD 0 : ℚ) : ℝ)| ≤ c.δ)
    (h0' : |φ c.t0 - ((c.pp.headD 0 : ℚ) : ℝ)| ≤ c.δ) :
    0 < θ c.t0 ∧ θ (c.t0 + c.h) < 0 ∧ (∀ t ∈ Icc (c.t0 : ℝ) (c.t0 + c.h), φ t < 0) ∧
      ∀ t ∈ Icc (c.t0 : ℝ) (c.t0 + c.h), (wlo : ℝ) ≤ -(t ^ 2 * φ t) ∧ -(t ^ 2 * φ t) ≤ whi := by
  have hc := cell_q c hok hθ hφ h0 h0'
  obtain ⟨-, -, k3⟩ := cellOK_basic c hok
  have hh : (0 : ℝ) < c.h := by exact_mod_cast k3
  obtain ⟨l1, l2, l3, l4, l5⟩ := of_decide_eq_true hl
  have r1 : ((0 : ℚ) : ℝ) < ((c.pt.headD 0 - c.δ : ℚ) : ℝ) := by exact_mod_cast l1
  have r2 : ((qeval c.pt c.h + c.B : ℚ) : ℝ) < ((0 : ℚ) : ℝ) := by exact_mod_cast l2
  have r3 : ((c.pp.headD 0 + c.h * qabs c.pp.tail c.h + c.B : ℚ) : ℝ) < ((0 : ℚ) : ℝ) := by
    exact_mod_cast l3
  have r4 : (wlo : ℝ) ≤ ((-((ucube c).headD 0 + c.h * qabs (ucube c).tail c.h) -
      (c.t0 + c.h) ^ 2 * c.B : ℚ) : ℝ) := by exact_mod_cast l4
  have r5 : ((-((ucube c).headD 0 - c.h * qabs (ucube c).tail c.h) + (c.t0 + c.h) ^ 2 * c.B : ℚ) :
      ℝ) ≤ whi := by exact_mod_cast l5
  push_cast at r1 r2 r3 r4 r5
  refine ⟨?_, ?_, fun t ht => ?_, fun t ht => ?_⟩
  · have := (abs_le.1 h0).1; linarith
  · have e := (hc (c.t0 + c.h) ⟨by linarith, le_rfl⟩).1
    rw [add_sub_cancel_left, ← qeval_cast, abs_le] at e
    linarith [e.2]
  · have hσ : t - c.t0 ∈ Icc (0 : ℝ) c.h := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have e := abs_le.1 (hc t ht).2
    have hu := upper_q c.pp hσ.1 hσ.2
    push_cast at hu
    linarith [e.2]
  · have hσ : t - c.t0 ∈ Icc (0 : ℝ) c.h := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have e := (hc t ht).2
    have hU : evalQ (ucube c) (t - c.t0) = t ^ 2 * evalQ c.pp (t - c.t0) := by
      simp only [ucube, evalQ_qmul, evalQ]; push_cast; ring
    have hlo := lower_q (ucube c) hσ.1 hσ.2
    have hhi := upper_q (ucube c) hσ.1 hσ.2
    push_cast at hlo hhi
    rw [hU] at hlo hhi
    have ht0 : (0 : ℝ) ≤ t := by
      have : (0 : ℝ) < c.t0 := by exact_mod_cast (cellOK_basic c hok).1
      linarith [ht.1]
    have ht2 : t ^ 2 ≤ ((c.t0 : ℝ) + c.h) ^ 2 := pow_le_pow_left₀ ht0 ht.2 2
    have hB0 : (0 : ℝ) ≤ c.B := (abs_nonneg _).trans e
    have hd : |t ^ 2 * φ t - t ^ 2 * evalQ c.pp (t - c.t0)| ≤ ((c.t0 : ℝ) + c.h) ^ 2 * c.B := by
      rw [← mul_sub, abs_mul, abs_of_nonneg (sq_nonneg t)]
      exact mul_le_mul ht2 e (abs_nonneg _) (sq_nonneg _)
    rw [abs_le] at hd
    constructor <;> linarith [hd.1, hd.2]

end Checked.Math.LE52Glue
