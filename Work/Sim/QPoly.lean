import Mathlib
import Work.Sim.ODETools

/-!
# Rational polynomial arithmetic evaluated by the kernel (run 2026-11-07T0828Z)

Validated-simulation certificates used to prove every polynomial identity of a cell (the
defect of a Taylor approximation) by `ring` over ℝ: the proof terms were large (≈ 6 MB of
olean per Townes cell) and the export for the independent checker grew with them. Here the
same identities are *computed*: polynomials are coefficient lists over ℚ (constant first, the
convention of `Work.Sim.evalQ`), `qadd`, `qsmul`, `qmul`, `qderiv` compute sums, products and
derivatives exactly, and the cast lemmas (`evalQ_qadd`, `evalQ_qmul`, `dEvalQ_eq`, …) say that
evaluating the computed list at a real point is the corresponding real expression. A cell's
defect bound then becomes a Boolean check over ℚ that the kernel decides by evaluation
(`decide +kernel`, exact GMP arithmetic, no extra axiom).
-/

namespace Work.Sim.QPoly
open Work.Sim

/-- Sum of coefficient lists. -/
def qadd : List ℚ → List ℚ → List ℚ
  | [], q => q
  | a :: p, [] => a :: p
  | a :: p, b :: q => (a + b) :: qadd p q

/-- Scalar multiple. -/
def qsmul (c : ℚ) : List ℚ → List ℚ
  | [] => []
  | a :: p => (c * a) :: qsmul c p

/-- Difference. -/
def qsub (p q : List ℚ) : List ℚ := qadd p (qsmul (-1) q)

/-- Product (schoolbook convolution). -/
def qmul : List ℚ → List ℚ → List ℚ
  | [], _ => []
  | a :: p, q => qadd (qsmul a q) (0 :: qmul p q)

/-- Derivative, following the product rule on Horner's form (`Work.Sim.dEvalQ`). -/
def qderiv : List ℚ → List ℚ
  | [] => []
  | _ :: p => qadd p (0 :: qderiv p)

/-- Horner evaluation over ℚ. -/
def qeval : List ℚ → ℚ → ℚ
  | [], _ => 0
  | c :: p, x => c + x * qeval p x

/-- Σ |cₖ| hᵏ: the bound of a polynomial on [0, h] by its absolute coefficients. -/
def qabs (p : List ℚ) (h : ℚ) : ℚ := qeval (p.map (fun c => |c|)) h

theorem evalQ_qadd (p q : List ℚ) (s : ℝ) : evalQ (qadd p q) s = evalQ p s + evalQ q s := by
  induction p generalizing q with
  | nil => simp [qadd, evalQ]
  | cons a p ih =>
    cases q with
    | nil => simp [qadd, evalQ]
    | cons b q => simp only [qadd, evalQ, ih]; push_cast; ring

theorem evalQ_qsmul (c : ℚ) (p : List ℚ) (s : ℝ) : evalQ (qsmul c p) s = c * evalQ p s := by
  induction p with
  | nil => simp [qsmul, evalQ]
  | cons a p ih => simp only [qsmul, evalQ, ih]; push_cast; ring

theorem evalQ_qsub (p q : List ℚ) (s : ℝ) : evalQ (qsub p q) s = evalQ p s - evalQ q s := by
  simp only [qsub, evalQ_qadd, evalQ_qsmul]; push_cast; ring

theorem evalQ_cons0 (p : List ℚ) (s : ℝ) : evalQ (0 :: p) s = s * evalQ p s := by
  simp [evalQ]

theorem evalQ_qmul (p q : List ℚ) (s : ℝ) : evalQ (qmul p q) s = evalQ p s * evalQ q s := by
  induction p with
  | nil => simp [qmul, evalQ]
  | cons a p ih => simp only [qmul, evalQ_qadd, evalQ_qsmul, ih, evalQ]; ring

theorem dEvalQ_eq (p : List ℚ) (s : ℝ) : dEvalQ p s = evalQ (qderiv p) s := by
  induction p with
  | nil => simp [qderiv, dEvalQ, evalQ]
  | cons a p ih => simp only [dEvalQ, qderiv, evalQ_qadd, evalQ_cons0, ih]

theorem qeval_cast (p : List ℚ) (x : ℚ) : ((qeval p x : ℚ) : ℝ) = evalQ p (x : ℝ) := by
  induction p with
  | nil => simp [qeval, evalQ]
  | cons c p ih => simp only [qeval, evalQ]; push_cast; rw [ih]

/-- |p(σ)| ≤ Σ|cₖ|hᵏ on [0, h], with the right side computed over ℚ. -/
theorem abs_le_qabs (p : List ℚ) {h : ℚ} {σ : ℝ} (h0 : 0 ≤ σ) (h1 : σ ≤ h) :
    |evalQ p σ| ≤ (qabs p h : ℝ) := by
  rw [qabs, qeval_cast]; exact abs_evalQ_le p h0 h1

/-- Lower bound c₀ − h·Σ|cₖ₊₁|hᵏ ≤ p(σ) on [0, h], computed over ℚ. -/
theorem lower_q (p : List ℚ) {h : ℚ} {σ : ℝ} (h0 : 0 ≤ σ) (h1 : σ ≤ h) :
    ((p.headD 0 - h * qabs p.tail h : ℚ) : ℝ) ≤ evalQ p σ := by
  cases p with
  | nil => simp [evalQ, qabs, qeval]
  | cons c cs =>
    have := evalQ_ge c cs h0 h1
    simp only [List.headD_cons, List.tail_cons, qabs]
    push_cast; rw [qeval_cast]; exact this

/-- Upper bound p(σ) ≤ c₀ + h·Σ|cₖ₊₁|hᵏ on [0, h], computed over ℚ. -/
theorem upper_q (p : List ℚ) {h : ℚ} {σ : ℝ} (h0 : 0 ≤ σ) (h1 : σ ≤ h) :
    evalQ p σ ≤ ((p.headD 0 + h * qabs p.tail h : ℚ) : ℝ) := by
  cases p with
  | nil => simp [evalQ, qabs, qeval]
  | cons c cs =>
    have := evalQ_le c cs h0 h1
    simp only [List.headD_cons, List.tail_cons, qabs]
    push_cast; rw [qeval_cast]; exact this

theorem evalQ_zero_head (p : List ℚ) : evalQ p 0 = ((p.headD 0 : ℚ) : ℝ) := by
  cases p with
  | nil => simp [evalQ]
  | cons c cs => simp [evalQ]

end Work.Sim.QPoly
