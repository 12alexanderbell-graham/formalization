import Mathlib
import Checked.Sim.ODETools

/-!
# Certified Chebyshev bounds for polynomials with rational coefficients

A polynomial q of degree n on [−1, 1] written in the monomial basis can have coefficients far
larger than its maximum (cancellation); the bound Σ|aₖ| then overestimates |q| by up to
≈ (1 + √2)ⁿ. Written in the Chebyshev basis, q = Σ bₖ Tₖ, the bound Σ|bₖ| is nearly tight
because |Tₖ(s)| ≤ 1 on [−1, 1].

`chebMono b` computes, by exact rational arithmetic (Clenshaw's recurrence on coefficient lists),
the monomial coefficients of Σ bₖ Tₖ(s). A generator supplies b; the equation
`chebMono b = a` is checked by evaluation in the kernel, and `cheb_bound` gives
|q(s)| ≤ Σ|bₖ| for |s| ≤ 1. Used for the defect bounds of the long-horizon Robertson cells,
where monomial bounds lose 10⁴–10⁹.
-/

namespace Work.Sim.ChebBound
open Polynomial Polynomial.Chebyshev Checked.Sim

/-- Sum of coefficient lists. -/
def padd : List ℚ → List ℚ → List ℚ
  | [], q => q
  | a :: p, [] => a :: p
  | a :: p, b :: q => (a + b) :: padd p q

/-- Scalar multiple. -/
def psmul (c : ℚ) : List ℚ → List ℚ
  | [] => []
  | a :: p => (c * a) :: psmul c p

/-- Clenshaw's recurrence on coefficient lists: for b = [b₀, …, bₙ] returns (Y₀, Y₁) with
Yₖ = bₖ + 2 s Yₖ₊₁ − Yₖ₊₂ (as polynomials in s). -/
def clenP : List ℚ → List ℚ × List ℚ
  | [] => ([], [])
  | b :: l =>
    let r := clenP l
    (padd [b] (padd (0 :: psmul 2 r.1) (psmul (-1) r.2)), r.1)

/-- Monomial coefficients of Σ bₖ Tₖ(s): Y₀ − s Y₁. -/
def chebMono (l : List ℚ) : List ℚ :=
  padd (clenP l).1 (0 :: psmul (-1) (clenP l).2)

/-- Σ |bₖ|. -/
def sumAbs : List ℚ → ℚ
  | [] => 0
  | b :: l => |b| + sumAbs l

theorem evalQ_padd (p q : List ℚ) (s : ℝ) : evalQ (padd p q) s = evalQ p s + evalQ q s := by
  induction p generalizing q with
  | nil => simp [padd, evalQ]
  | cons a p ih =>
    cases q with
    | nil => simp [padd, evalQ]
    | cons b q => simp only [padd, evalQ, ih]; push_cast; ring

theorem evalQ_psmul (c : ℚ) (p : List ℚ) (s : ℝ) : evalQ (psmul c p) s = c * evalQ p s := by
  induction p with
  | nil => simp [psmul, evalQ]
  | cons a p ih => simp only [psmul, evalQ, ih]; push_cast; ring

theorem evalQ_cons0 (p : List ℚ) (s : ℝ) : evalQ (0 :: p) s = s * evalQ p s := by
  simp [evalQ]

/-- Σₖ bₖ U_{j+k}(s). -/
noncomputable def Us : List ℚ → ℤ → ℝ → ℝ
  | [], _, _ => 0
  | b :: l, j, s => (b : ℝ) * (U ℝ j).eval s + Us l (j + 1) s

/-- Σₖ bₖ T_{j+k}(s). -/
noncomputable def Ts : List ℚ → ℤ → ℝ → ℝ
  | [], _, _ => 0
  | b :: l, j, s => (b : ℝ) * (T ℝ j).eval s + Ts l (j + 1) s

theorem Us_rec (l : List ℚ) (j : ℤ) (s : ℝ) :
    Us l (j + 1) s = 2 * s * Us l j s - Us l (j - 1) s := by
  induction l generalizing j with
  | nil => simp [Us]
  | cons b l ih =>
    have hU : (U ℝ (j + 1)).eval s = 2 * s * (U ℝ j).eval s - (U ℝ (j - 1)).eval s := by
      have := U_add_two ℝ (j - 1)
      rw [show j - 1 + 2 = j + 1 by ring, show j - 1 + 1 = j by ring] at this
      rw [this]; simp
    simp only [Us]
    rw [hU, show j + 1 + 1 = (j + 1) + 1 by ring, ih (j + 1), show j - 1 + 1 = j by ring,
      show j + 1 - 1 = j by ring]
    ring

theorem clenP_eval (l : List ℚ) (s : ℝ) :
    evalQ (clenP l).1 s = Us l 0 s ∧ evalQ (clenP l).2 s = Us l (-1) s := by
  induction l with
  | nil => simp [clenP, evalQ, Us]
  | cons b l ih =>
    obtain ⟨h1, h2⟩ := ih
    have hr := Us_rec l 0 s
    simp only [zero_add, zero_sub] at hr
    constructor
    · simp only [clenP, evalQ_padd, evalQ_psmul, evalQ_cons0, h1, h2, Us]
      simp [evalQ, U_zero]
      rw [hr]; ring
    · simp only [clenP, h1, Us]
      simp [U_neg_one]

theorem Us_Ts (l : List ℚ) (j : ℤ) (s : ℝ) : Us l j s - s * Us l (j - 1) s = Ts l j s := by
  induction l generalizing j with
  | nil => simp [Us, Ts]
  | cons b l ih =>
    have hT : (T ℝ j).eval s = (U ℝ j).eval s - s * (U ℝ (j - 1)).eval s := by
      rw [T_eq_U_sub_X_mul_U]; simp
    simp only [Us, Ts]
    rw [show j - 1 + 1 = j by ring, ← ih (j + 1), show j + 1 - 1 = j by ring, hT]
    ring

theorem chebMono_eval (l : List ℚ) (s : ℝ) : evalQ (chebMono l) s = Ts l 0 s := by
  obtain ⟨h1, h2⟩ := clenP_eval l s
  rw [chebMono, evalQ_padd, evalQ_cons0, evalQ_psmul, h1, h2, ← Us_Ts l 0 s,
    show (0 : ℤ) - 1 = -1 by norm_num]
  push_cast
  ring

theorem Ts_bound (l : List ℚ) (j : ℤ) {s : ℝ} (hs : |s| ≤ 1) : |Ts l j s| ≤ sumAbs l := by
  induction l generalizing j with
  | nil => simp [Ts, sumAbs]
  | cons b l ih =>
    simp only [Ts, sumAbs]
    push_cast
    have hT := abs_eval_T_real_le_one j hs
    calc |(b : ℝ) * (T ℝ j).eval s + Ts l (j + 1) s|
        ≤ |(b : ℝ) * (T ℝ j).eval s| + |Ts l (j + 1) s| := abs_add_le _ _
      _ ≤ |(b : ℝ)| * 1 + sumAbs l := by
          rw [abs_mul]
          gcongr
          · exact_mod_cast ih (j + 1)
      _ = |(b : ℝ)| + sumAbs l := by ring

/-- Chebyshev bound: |Σ bₖ Tₖ(s)| ≤ Σ |bₖ| on [−1, 1]. -/
theorem cheb_bound (l : List ℚ) {s : ℝ} (hs : |s| ≤ 1) :
    |evalQ (chebMono l) s| ≤ sumAbs l := by
  rw [chebMono_eval]; exact Ts_bound l 0 hs

/-- Range form: |Σ bₖ Tₖ(s) − b₀| ≤ Σ_{k ≥ 1} |bₖ| on [−1, 1]. -/
theorem cheb_range (b : ℚ) (l : List ℚ) {s : ℝ} (hs : |s| ≤ 1) :
    |evalQ (chebMono (b :: l)) s - b| ≤ sumAbs l := by
  rw [chebMono_eval]
  simp only [Ts, T_zero, eval_one, mul_one, zero_add, add_sub_cancel_left]
  exact_mod_cast Ts_bound l 1 hs

/-- Usage form: if the generated monomial list `a` equals `chebMono b` and q(u) = a(u / r), then
|q(u)| ≤ Σ|bₖ| for |u| ≤ r. -/
theorem bound_of_eq {a b : List ℚ} (hab : chebMono b = a) {r u : ℝ} (hr : 0 < r)
    (hu : |u| ≤ r) : |evalQ a (u / r)| ≤ sumAbs b := by
  rw [← hab]
  apply cheb_bound
  rw [abs_div, abs_of_pos hr, div_le_one hr]; exact hu

/-- Rescaling helper: coefficients aₖ m rᵏ. -/
def scaleGo : List ℚ → ℚ → ℚ → List ℚ
  | [], _, _ => []
  | a :: l, m, r => (a * m) :: scaleGo l (m * r) r

/-- Rescaling: coefficients aₖ rᵏ. -/
def scaleL (l : List ℚ) (r : ℚ) : List ℚ := scaleGo l 1 r

theorem evalQ_scaleGo (l : List ℚ) (m r : ℚ) (s : ℝ) :
    evalQ (scaleGo l m r) s = m * evalQ l (r * s) := by
  induction l generalizing m with
  | nil => simp [scaleGo, evalQ]
  | cons a l ih =>
    simp only [scaleGo, evalQ, ih]; push_cast; ring

theorem evalQ_scaleL (l : List ℚ) (r : ℚ) (s : ℝ) :
    evalQ (scaleL l r) s = evalQ l (r * s) := by
  simp [scaleL, evalQ_scaleGo]

/-- Range of a polynomial on [−r, r] from its Chebyshev coefficients. -/
theorem range_of_eq {a : List ℚ} {b : ℚ} {l : List ℚ} {r : ℚ}
    (hab : chebMono (b :: l) = scaleL a r) (hr : 0 < r) {u : ℝ} (hu : |u| ≤ r) :
    b - sumAbs l ≤ evalQ a u ∧ evalQ a u ≤ b + sumAbs l := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have h := cheb_range b l (s := u / r) (by
    rw [abs_div, abs_of_pos hr', div_le_one hr']; exact hu)
  rw [hab, evalQ_scaleL, mul_div_cancel₀ _ hr'.ne'] at h
  rw [abs_le] at h
  constructor <;> linarith [h.1, h.2]

-- sanity check: 1 + 2 T₁ + 3 T₂ = 1 + 2 s + 3 (2 s² − 1) = −2 + 2 s + 6 s²
example : chebMono [1, 2, 3] = [-2, 2, 6] := by decide +kernel
example : scaleL [1, 2, 3] 2 = [1, 4, 12] := by decide +kernel

end Work.Sim.ChebBound

#print axioms Work.Sim.ChebBound.cheb_bound
#print axioms Work.Sim.ChebBound.cheb_range
