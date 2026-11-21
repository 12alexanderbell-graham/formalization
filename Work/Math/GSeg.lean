import Mathlib
import Work.Math.GContract

open Set

/-! Gelfand problem, `GSeg` (run 2026-11-21T0428Z): contracting homology cells with facts on the whole cell.
`Work.Math.GContract.ccell_q` bounds the error only at a cell's end; here the bound inside the cell
(`ccell_in`: Q of the error is at most the start bound plus the Grönwall floor, `inB`), a link lemma between
cells (`link_q`), and a chain with a property checked on every cell (`seg_all`: if every cell's polynomials plus
the in-cell error satisfy a relation, every solution value on the chain's range does). The predicates used
are rational checks decided by the kernel: v below or above a level (`vLtP`, `vGtP`) and u inside an interval
(`uInP`). Also the change to log radius of the homology system in the radius (`log_radius`) and bounds on
the exponential function from partial sums (`exp_ge_sum`, `exp_le_pow4`). -/

namespace Work.Math.GSeg

open Work.Math.GContract Checked.Sim Checked.Sim.QPoly Checked.Math.GCellQ

noncomputable section

/-- The in-cell bound of Q of the error: start bound plus the Grönwall floor 4η²/κ/(−(2μ + κ)). -/
def inB (c : CCell) : ℚ := c.δ + 4 * c.η ^ 2 / c.κ / -(2 * c.μ + c.κ)

/-- One contracting cell, bound inside the cell. -/
theorem ccell_in (c : CCell) (hok : decide (CCProp c) = true) {τ₀ : ℝ} {u v : ℝ → ℝ}
    (hu : ∀ t ∈ Icc τ₀ (τ₀ + c.h), HasDerivWithinAt u (F1 (u t) (v t)) (Icc τ₀ (τ₀ + c.h)) t)
    (hv : ∀ t ∈ Icc τ₀ (τ₀ + c.h), HasDerivWithinAt v (F2 (u t) (v t)) (Icc τ₀ (τ₀ + c.h)) t)
    (h0 : Q (u τ₀ - evalQ c.pu 0) (v τ₀ - evalQ c.pv 0) ≤ c.δ) :
    ∀ t ∈ Icc τ₀ (τ₀ + c.h),
      Q (u t - evalQ c.pu (t - τ₀)) (v t - evalQ c.pv (t - τ₀)) ≤ ((inB c : ℚ) : ℝ) := by
  obtain ⟨k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14, k15, k16, k17, k18⟩ :
    CCProp c := of_decide_eq_true hok
  have r : ∀ {a b : ℚ}, a ≤ b → (a : ℝ) ≤ (b : ℝ) := fun h => by exact_mod_cast h
  have rl : ∀ {a b : ℚ}, a < b → (a : ℝ) < (b : ℝ) := fun h => by exact_mod_cast h
  have hh := rl k0; have hκ := rl k1; have hρ := rl k2; have hδ := r k3; have hη := r k4
  have hK := rl k5; have r6 := r k6; have r7 := r k7; have r8 := r k8; have r9 := r k9
  have r10 := r k10; have r11 := r k11; have r12 := rl k12; have r13 := rl k13
  push_cast at hh hκ hρ hδ hη hK r12 r13
  set p : ℝ → ℝ := fun t => evalQ c.pu (t - τ₀) with hp
  set q : ℝ → ℝ := fun t => evalQ c.pv (t - τ₀) with hq
  have hs : ∀ t ∈ Icc τ₀ (τ₀ + c.h), (0 : ℝ) ≤ t - τ₀ ∧ t - τ₀ ≤ c.h := fun t ht =>
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have dp : ∀ t ∈ Icc τ₀ (τ₀ + c.h),
      HasDerivWithinAt p (evalQ (qderiv c.pu) (t - τ₀)) (Icc τ₀ (τ₀ + c.h)) t := by
    intro t _
    have := (hasDerivAt_evalQ c.pu (t - τ₀)).comp t ((hasDerivAt_id t).sub_const τ₀)
    rw [dEvalQ_eq, mul_one] at this; exact this.hasDerivWithinAt
  have dq : ∀ t ∈ Icc τ₀ (τ₀ + c.h),
      HasDerivWithinAt q (evalQ (qderiv c.pv) (t - τ₀)) (Icc τ₀ (τ₀ + c.h)) t := by
    intro t _
    have := (hasDerivAt_evalQ c.pv (t - τ₀)).comp t ((hasDerivAt_id t).sub_const τ₀)
    rw [dEvalQ_eq, mul_one] at this; exact this.hasDerivWithinAt
  have ddu : ∀ t ∈ Ico τ₀ (τ₀ + c.h), |evalQ (qderiv c.pu) (t - τ₀) - F1 (p t) (q t)| ≤ c.η := by
    intro t ht
    have e : evalQ (qderiv c.pu) (t - τ₀) - F1 (p t) (q t) = evalQ (cdu c) (t - τ₀) := by
      simp only [cdu, evalQ_qsub, evalQ_qmul, F1, hp, hq]; simp [evalQ]
    rw [e]
    have hs' := hs t (Ico_subset_Icc_self ht)
    exact (abs_le_qabs _ hs'.1 hs'.2).trans r6
  have ddv : ∀ t ∈ Ico τ₀ (τ₀ + c.h), |evalQ (qderiv c.pv) (t - τ₀) - F2 (p t) (q t)| ≤ c.η := by
    intro t ht
    have e : evalQ (qderiv c.pv) (t - τ₀) - F2 (p t) (q t) = evalQ (cdv c) (t - τ₀) := by
      simp only [cdv, evalQ_qsub, evalQ_qmul, F2, hp, hq]; simp [evalQ]
    rw [e]
    have hs' := hs t (Ico_subset_Icc_self ht)
    exact (abs_le_qabs _ hs'.1 hs'.2).trans r7
  have hpin : ∀ t ∈ Icc τ₀ (τ₀ + c.h), ((c.a₀ : ℝ) + c.ρ ≤ p t ∧ p t ≤ (c.a₁ : ℝ) - c.ρ) ∧
      ((c.b₀ : ℝ) + c.ρ ≤ q t ∧ q t ≤ (c.b₁ : ℝ) - c.ρ) := by
    intro t ht
    obtain ⟨s0, s1⟩ := hs t ht
    have l1 := lo_le c.pu s0 s1; have u1 := le_hi c.pu s0 s1
    have l2 := lo_le c.pv s0 s1; have u2 := le_hi c.pv s0 s1
    push_cast at r8 r9 r10 r11
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  set K : ℝ := 2 * c.μ + c.κ
  set C : ℝ := 4 * (c.η : ℝ) ^ 2 / c.κ
  have hδ0 : Q (u τ₀ - p τ₀) (v τ₀ - q τ₀) ≤ c.δ := by simpa [hp, hq] using h0
  have hG : ∀ t ∈ Icc τ₀ (τ₀ + c.h),
      gronwallBound (Q (u τ₀ - p τ₀) (v τ₀ - q τ₀)) K C (t - τ₀) < 2 * (c.ρ : ℝ) ^ 2 := by
    intro t ht
    have := gb_le_max (δ := Q (u τ₀ - p τ₀) (v τ₀ - q τ₀)) (ε := C) hK (hs t ht).1
    refine lt_of_le_of_lt this (max_lt (by linarith) ?_)
    simpa [C, K] using r13
  have main := contract_boot (a₀ := c.a₀) (a₁ := c.a₁) (b₀ := c.b₀) (b₁ := c.b₁) (μ := c.μ) hκ hρ hu hv dp dq
    ddu ddv hpin hG (cornerQ_real k15) (cornerQ_real k16) (cornerQ_real k17) (cornerQ_real k18)
  intro t ht
  have h1 := main t ht
  have h2 := gb_le_max (δ := Q (u τ₀ - p τ₀) (v τ₀ - q τ₀)) (ε := C) hK (hs t ht).1
  have hC : 0 ≤ C / -K := div_nonneg (by positivity) (by linarith)
  have e : ((inB c : ℚ) : ℝ) = (c.δ : ℝ) + C / -K := by
    simp only [inB, C, K]; push_cast; ring
  rw [e]
  have h3 : max (Q (u τ₀ - p τ₀) (v τ₀ - q τ₀)) (C / -K) ≤ (c.δ : ℝ) + C / -K :=
    max_le (by linarith) (by linarith)
  exact h1.trans (h2.trans h3)

/-- The link from cell `c` to cell `d`: `c`'s end bound gives `d`'s start bound. -/
theorem link_q {c d : CCell} (hl : decide (LinkProp c d) = true) {x y : ℝ}
    (hB : Q (x - evalQ c.pu c.h) (y - evalQ c.pv c.h) ≤ c.B) :
    Q (x - evalQ d.pu 0) (y - evalQ d.pv 0) ≤ d.δ := by
  have hl' : LinkProp c d := of_decide_eq_true hl
  unfold LinkProp at hl'
  have hq := Q_add_le (θ := 1 / 1000) (by norm_num)
    (x - evalQ c.pu c.h) (y - evalQ c.pv c.h)
    (evalQ c.pu c.h - evalQ d.pu 0) (evalQ c.pv c.h - evalQ d.pv 0)
  have hL : ((1 + 1 / 1000 : ℚ) : ℝ) * c.B +
      ((1 + 1000 : ℚ) : ℝ) * ((Qq (d.pu.headD 0 - qeval c.pu c.h) (d.pv.headD 0 - qeval c.pv c.h) : ℚ) : ℝ)
      ≤ d.δ := by exact_mod_cast hl'
  rw [Qq_cast] at hL
  have hr : Q (evalQ c.pu c.h - evalQ d.pu 0) (evalQ c.pv c.h - evalQ d.pv 0) =
      Q (((d.pu.headD 0 - qeval c.pu c.h : ℚ) : ℝ)) (((d.pv.headD 0 - qeval c.pv c.h : ℚ) : ℝ)) := by
    rw [evalQ_headD, evalQ_headD]; push_cast; rw [qeval_cast, qeval_cast]; unfold Q; ring
  have e1 : x - evalQ c.pu c.h + (evalQ c.pu c.h - evalQ d.pu 0) = x - evalQ d.pu 0 := by ring
  have e2 : y - evalQ c.pv c.h + (evalQ c.pv c.h - evalQ d.pv 0) = y - evalQ d.pv 0 := by ring
  rw [e1, e2, hr] at hq
  push_cast at hL hq
  nlinarith

/-- A chain of contracting cells with a property on every cell: when every cell's property turns the in-cell
bound into a relation between the solution's two values, the relation holds on the chain's whole range. -/
theorem seg_all (R : ℝ → ℝ → Prop) (P : CCell → Prop)
    (hPR : ∀ c, P c → ∀ x a b : ℝ, 0 ≤ x → x ≤ c.h →
      Q (a - evalQ c.pu x) (b - evalQ c.pv x) ≤ ((inB c : ℚ) : ℝ) → R a b) :
    ∀ (cs : List CCell) (c : CCell), chainOK (c :: cs) = true → (∀ d ∈ c :: cs, P d) →
    ∀ {τ₀ : ℝ} {u v : ℝ → ℝ},
    (∀ t ∈ Icc τ₀ (τ₀ + totalH (c :: cs)),
      HasDerivWithinAt u (F1 (u t) (v t)) (Icc τ₀ (τ₀ + totalH (c :: cs))) t) →
    (∀ t ∈ Icc τ₀ (τ₀ + totalH (c :: cs)),
      HasDerivWithinAt v (F2 (u t) (v t)) (Icc τ₀ (τ₀ + totalH (c :: cs))) t) →
    Q (u τ₀ - evalQ c.pu 0) (v τ₀ - evalQ c.pv 0) ≤ c.δ →
    ∀ t ∈ Icc τ₀ (τ₀ + totalH (c :: cs)), R (u t) (v t)
  | [], c, hok, hP, τ₀, u, v, hu, hv, h0 => by
      have e : ((totalH [c] : ℚ) : ℝ) = (c.h : ℝ) := by simp [totalH]
      rw [e] at hu hv ⊢
      intro t ht
      have hin := ccell_in c (by simpa [chainOK] using hok) hu hv h0 t ht
      exact hPR c (hP c (by simp)) (t - τ₀) _ _ (by linarith [ht.1]) (by linarith [ht.2]) hin
  | d :: ds, c, hok, hP, τ₀, u, v, hu, hv, h0 => by
      simp only [chainOK, Bool.and_eq_true, decide_eq_true_eq] at hok
      obtain ⟨⟨hc, hl⟩, hrest⟩ := hok
      have hT : ((totalH (c :: d :: ds) : ℚ) : ℝ) = (c.h : ℝ) + ((totalH (d :: ds) : ℚ) : ℝ) := by
        simp only [totalH]; push_cast; ring
      have hnn : (0 : ℝ) ≤ ((totalH (d :: ds) : ℚ) : ℝ) := by exact_mod_cast totalH_nonneg _ hrest
      have hh : (0 : ℝ) < c.h := by exact_mod_cast hc.1
      rw [hT] at hu hv ⊢
      have sub1 : Icc τ₀ (τ₀ + (c.h : ℝ)) ⊆ Icc τ₀ (τ₀ + ((c.h : ℝ) + totalH (d :: ds))) :=
        Icc_subset_Icc_right (by linarith)
      have sub2 : Icc (τ₀ + c.h) (τ₀ + c.h + ((totalH (d :: ds) : ℚ) : ℝ)) ⊆
          Icc τ₀ (τ₀ + ((c.h : ℝ) + totalH (d :: ds))) :=
        Icc_subset_Icc (by linarith) (by linarith)
      have hu1 := fun t (ht : t ∈ Icc τ₀ (τ₀ + (c.h : ℝ))) => (hu t (sub1 ht)).mono sub1
      have hv1 := fun t (ht : t ∈ Icc τ₀ (τ₀ + (c.h : ℝ))) => (hv t (sub1 ht)).mono sub1
      have end1 := ccell_q c (by simpa using hc) (τ₀ := τ₀) hu1 hv1 h0
      have link := link_q (c := c) (d := d) (by simpa using hl) end1
      intro t ht
      rcases le_or_gt t (τ₀ + c.h) with h | h
      · have hin := ccell_in c (by simpa using hc) hu1 hv1 h0 t ⟨ht.1, h⟩
        exact hPR c (hP c (by simp)) (t - τ₀) _ _ (by linarith [ht.1]) (by linarith) hin
      · have ih := seg_all R P hPR ds d (by simpa using hrest) (fun e he => hP e (by simp [he]))
          (τ₀ := τ₀ + c.h) (fun t ht => (hu t (sub2 ht)).mono sub2)
          (fun t ht => (hv t (sub2 ht)).mono sub2) link
        exact ih t ⟨h.le, by linarith [ht.2]⟩

/-! ## Cell predicates -/

/-- v stays below `y` on the cell. -/
def vLtP (y : ℚ) (c : CCell) : Prop := hi c.pv c.h < y ∧ 2 * inB c < (y - hi c.pv c.h) ^ 2
/-- v stays above `y` on the cell. -/
def vGtP (y : ℚ) (c : CCell) : Prop := y < lo c.pv c.h ∧ 2 * inB c < (lo c.pv c.h - y) ^ 2
/-- u stays strictly between `L` and `U` on the cell. -/
def uInP (L U : ℚ) (c : CCell) : Prop :=
  L < lo c.pu c.h ∧ 2 * inB c < (lo c.pu c.h - L) ^ 2 ∧ hi c.pu c.h < U ∧ 2 * inB c < (U - hi c.pu c.h) ^ 2

instance (y : ℚ) (c : CCell) : Decidable (vLtP y c) := by unfold vLtP; infer_instance
instance (y : ℚ) (c : CCell) : Decidable (vGtP y c) := by unfold vGtP; infer_instance
instance (L U : ℚ) (c : CCell) : Decidable (uInP L U c) := by unfold uInP; infer_instance

def vLtB (y : ℚ) (c : CCell) : Bool := decide (vLtP y c)
def vGtB (y : ℚ) (c : CCell) : Bool := decide (vGtP y c)
def uInB (L U : ℚ) (c : CCell) : Bool := decide (uInP L U c)

theorem err_sq {a b d : ℝ} (h : Q a b ≤ d) : a ^ 2 ≤ 2 * d ∧ b ^ 2 ≤ 2 * d := by
  have := Q_ge a b
  constructor <;> nlinarith [sq_nonneg a, sq_nonneg b]

/-- |e| < m from e² ≤ 2d < m² with m > 0. -/
theorem abs_lt_of {e d m : ℝ} (hm : 0 < m) (h1 : e ^ 2 ≤ 2 * d) (h2 : 2 * d < m ^ 2) : |e| < m := by
  have : e ^ 2 < m ^ 2 := lt_of_le_of_lt h1 h2
  exact abs_lt_of_sq_lt_sq this hm.le

theorem vLt_rel (y : ℚ) : ∀ c, (vLtB y c = true) → ∀ x a b : ℝ, 0 ≤ x → x ≤ c.h →
    Q (a - evalQ c.pu x) (b - evalQ c.pv x) ≤ ((inB c : ℚ) : ℝ) → b < y := by
  intro c hc x a b h0 h1 hQ
  have hp : vLtP y c := of_decide_eq_true hc
  obtain ⟨k1, k2⟩ := hp
  have r1 : ((hi c.pv c.h : ℚ) : ℝ) < y := by exact_mod_cast k1
  have r2 : 2 * ((inB c : ℚ) : ℝ) < ((y : ℝ) - (hi c.pv c.h : ℚ)) ^ 2 := by exact_mod_cast k2
  have := abs_lt_of (by linarith) (err_sq hQ).2 r2
  have hh := le_hi c.pv h0 h1
  have := (abs_lt.1 this).2
  linarith

theorem vGt_rel (y : ℚ) : ∀ c, (vGtB y c = true) → ∀ x a b : ℝ, 0 ≤ x → x ≤ c.h →
    Q (a - evalQ c.pu x) (b - evalQ c.pv x) ≤ ((inB c : ℚ) : ℝ) → (y : ℝ) < b := by
  intro c hc x a b h0 h1 hQ
  have hp : vGtP y c := of_decide_eq_true hc
  obtain ⟨k1, k2⟩ := hp
  have r1 : (y : ℝ) < ((lo c.pv c.h : ℚ) : ℝ) := by exact_mod_cast k1
  have r2 : 2 * ((inB c : ℚ) : ℝ) < (((lo c.pv c.h : ℚ) : ℝ) - y) ^ 2 := by exact_mod_cast k2
  have := abs_lt_of (by linarith) (err_sq hQ).2 r2
  have hh := lo_le c.pv h0 h1
  have := (abs_lt.1 this).1
  linarith

theorem uIn_rel (L U : ℚ) : ∀ c, (uInB L U c = true) → ∀ x a b : ℝ, 0 ≤ x → x ≤ c.h →
    Q (a - evalQ c.pu x) (b - evalQ c.pv x) ≤ ((inB c : ℚ) : ℝ) → (L : ℝ) < a ∧ a < U := by
  intro c hc x a b h0 h1 hQ
  have hp : uInP L U c := of_decide_eq_true hc
  obtain ⟨k1, k2, k3, k4⟩ := hp
  have r1 : (L : ℝ) < ((lo c.pu c.h : ℚ) : ℝ) := by exact_mod_cast k1
  have r2 : 2 * ((inB c : ℚ) : ℝ) < (((lo c.pu c.h : ℚ) : ℝ) - L) ^ 2 := by exact_mod_cast k2
  have r3 : ((hi c.pu c.h : ℚ) : ℝ) < U := by exact_mod_cast k3
  have r4 : 2 * ((inB c : ℚ) : ℝ) < ((U : ℝ) - (hi c.pu c.h : ℚ)) ^ 2 := by exact_mod_cast k4
  have a1 := abs_lt_of (by linarith) (err_sq hQ).1 r2
  have a2 := abs_lt_of (by linarith) (err_sq hQ).1 r4
  have l := lo_le c.pu h0 h1
  have h := le_hi c.pu h0 h1
  constructor
  · linarith [(abs_lt.1 a1).1]
  · linarith [(abs_lt.1 a2).2]

/-- `List.all` of a Boolean predicate as membership. -/
theorem all_mem {p : CCell → Bool} {l : List CCell} (h : l.all p = true) : ∀ d ∈ l, p d = true := by
  simpa [List.all_eq_true] using h


/-! ## Chains given as named lists -/

/-- A placeholder cell (head of an empty list). -/
def dflt : CCell := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, [], []⟩
/-- The first cell of a chain. -/
def hd (l : List CCell) : CCell := l.headD dflt
/-- The last cell of a chain. -/
def lst (l : List CCell) : CCell := lastC l.tail (l.headD dflt)

/-- `chain_q` for a named nonempty list with its total length given. -/
theorem chain_end (l : List CCell) (L : ℚ) (hL : totalH l = L) (hok : chainOK l = true) (hne : l ≠ [])
    {τ₀ : ℝ} {u v : ℝ → ℝ}
    (hu : ∀ t ∈ Icc τ₀ (τ₀ + (L : ℝ)), HasDerivWithinAt u (F1 (u t) (v t)) (Icc τ₀ (τ₀ + (L : ℝ))) t)
    (hv : ∀ t ∈ Icc τ₀ (τ₀ + (L : ℝ)), HasDerivWithinAt v (F2 (u t) (v t)) (Icc τ₀ (τ₀ + (L : ℝ))) t)
    (h0 : Q (u τ₀ - evalQ (hd l).pu 0) (v τ₀ - evalQ (hd l).pv 0) ≤ (hd l).δ) :
    Q (u (τ₀ + L) - evalQ (lst l).pu (lst l).h) (v (τ₀ + L) - evalQ (lst l).pv (lst l).h) ≤ (lst l).B := by
  cases l with
  | nil => exact absurd rfl hne
  | cons c cs =>
    subst hL
    exact chain_q cs c hok hu hv h0

/-- `seg_all` for a named nonempty list with its total length given. -/
theorem seg_all' (R : ℝ → ℝ → Prop) (p : CCell → Bool)
    (hPR : ∀ c, p c = true → ∀ x a b : ℝ, 0 ≤ x → x ≤ c.h →
      Q (a - evalQ c.pu x) (b - evalQ c.pv x) ≤ ((inB c : ℚ) : ℝ) → R a b)
    (l : List CCell) (L : ℚ) (hL : totalH l = L) (hok : chainOK l = true) (hne : l ≠ [])
    (hall : l.all p = true) {τ₀ : ℝ} {u v : ℝ → ℝ}
    (hu : ∀ t ∈ Icc τ₀ (τ₀ + (L : ℝ)), HasDerivWithinAt u (F1 (u t) (v t)) (Icc τ₀ (τ₀ + (L : ℝ))) t)
    (hv : ∀ t ∈ Icc τ₀ (τ₀ + (L : ℝ)), HasDerivWithinAt v (F2 (u t) (v t)) (Icc τ₀ (τ₀ + (L : ℝ))) t)
    (h0 : Q (u τ₀ - evalQ (hd l).pu 0) (v τ₀ - evalQ (hd l).pv 0) ≤ (hd l).δ) :
    ∀ t ∈ Icc τ₀ (τ₀ + (L : ℝ)), R (u t) (v t) := by
  cases l with
  | nil => exact absurd rfl hne
  | cons c cs =>
    subst hL
    exact seg_all R (fun c => p c = true) hPR cs c hok (all_mem hall) hu hv h0

/-! ## Log radius and the exponential function -/

/-- The homology system in the radius becomes the autonomous system in log radius. -/
theorem log_radius {U V : ℝ → ℝ} {τ : ℝ}
    (hU : HasDerivAt U (U (Real.exp τ) * (3 - U (Real.exp τ) - V (Real.exp τ)) / Real.exp τ) (Real.exp τ))
    (hV : HasDerivAt V (V (Real.exp τ) * (U (Real.exp τ) - 1) / Real.exp τ) (Real.exp τ)) :
    HasDerivAt (fun x => U (Real.exp x)) (F1 (U (Real.exp τ)) (V (Real.exp τ))) τ ∧
    HasDerivAt (fun x => V (Real.exp x)) (F2 (U (Real.exp τ)) (V (Real.exp τ))) τ := by
  have he := Real.hasDerivAt_exp τ
  have hpos := Real.exp_pos τ
  constructor
  · have := hU.comp τ he
    refine this.congr_deriv ?_
    unfold F1; field_simp
  · have := hV.comp τ he
    refine this.congr_deriv ?_
    unfold F2; field_simp

/-- Partial sums of the exponential series bound it from below. -/
theorem exp_ge_sum {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    ∑ i ∈ Finset.range n, x ^ i / (Nat.factorial i) ≤ Real.exp x :=
  Real.sum_le_exp_of_nonneg hx n

/-- An upper bound of exp x from its fourth root and a partial sum with remainder. -/
theorem exp_le_pow4 {x : ℝ} (h1 : 0 ≤ x) (h2 : x ≤ 4) (n : ℕ) (hn : 0 < n) :
    Real.exp x ≤ ((∑ m ∈ Finset.range n, (x / 4) ^ m / m.factorial) +
      (x / 4) ^ n * (n + 1) / (n.factorial * n)) ^ 4 := by
  have e : Real.exp x = Real.exp (x / 4) ^ 4 := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  rw [e]
  have hb := Real.exp_bound' (x := x / 4) (by linarith) (by linarith) hn
  exact pow_le_pow_left₀ (Real.exp_pos _).le hb 4

end

end Work.Math.GSeg
