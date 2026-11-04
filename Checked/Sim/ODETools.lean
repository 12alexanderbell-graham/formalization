import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Complex.Exponential

/-!
# Rigorous simulation tools: rational polynomials and a validated Grönwall cell step

Generic tools for certified ODE enclosures (THE RESULT part 1, "rigorous simulators").
A polynomial with rational coefficients is a `List ℚ` evaluated by Horner's rule (`evalQ`);
`dEvalQ` is its derivative (`hasDerivAt_evalQ`), `abs_evalQ_le` bounds it on [0, h] by the
sum of |coefficients|·hᵏ, so every defect bound is one exact rational computation.
-/

namespace Checked.Sim
open Set

/-- Horner evaluation of the polynomial with rational coefficient list `cs` (constant first)
at the real number `s`. -/
def evalQ : List ℚ → ℝ → ℝ
  | [], _ => 0
  | c :: cs, s => (c : ℝ) + s * evalQ cs s

/-- Derivative of `evalQ cs` at `s`, by the product rule on Horner's form. -/
def dEvalQ : List ℚ → ℝ → ℝ
  | [], _ => 0
  | _ :: cs, s => evalQ cs s + s * dEvalQ cs s

theorem hasDerivAt_evalQ (cs : List ℚ) (s : ℝ) : HasDerivAt (evalQ cs) (dEvalQ cs s) s := by
  induction cs generalizing s with
  | nil => simpa [evalQ, dEvalQ] using hasDerivAt_const s (0 : ℝ)
  | cons c cs ih =>
    have h := (hasDerivAt_const s (c : ℝ)).add ((hasDerivAt_id s).mul (ih s))
    have hf : evalQ (c :: cs) = fun s => (c : ℝ) + id s * evalQ cs s := by
      funext s; simp [evalQ]
    rw [hf]; convert h using 1; simp [dEvalQ]

theorem continuous_evalQ (cs : List ℚ) : Continuous (evalQ cs) :=
  continuous_iff_continuousAt.2 fun s => (hasDerivAt_evalQ cs s).continuousAt

theorem abs_evalQ_le (cs : List ℚ) {s h : ℝ} (hs0 : 0 ≤ s) (hsh : s ≤ h) :
    |evalQ cs s| ≤ evalQ (cs.map (fun c => |c|)) h := by
  induction cs with
  | nil => simp [evalQ]
  | cons c cs ih =>
    simp only [evalQ, List.map_cons, Rat.cast_abs]
    have hA : 0 ≤ evalQ (cs.map (fun c => |c|)) h := (abs_nonneg _).trans ih
    calc |(c : ℝ) + s * evalQ cs s| ≤ |(c : ℝ)| + |s * evalQ cs s| := abs_add_le _ _
      _ = |(c : ℝ)| + s * |evalQ cs s| := by rw [abs_mul, abs_of_nonneg hs0]
      _ ≤ |(c : ℝ)| + h * evalQ (cs.map (fun c => |c|)) h :=
          add_le_add_right ((mul_le_mul_of_nonneg_left ih hs0).trans
            (mul_le_mul_of_nonneg_right hsh hA)) _

/-- Crude lower bound: c₀ − h·Σ|cₖ₊₁|hᵏ ≤ p(s) on [0, h]. -/
theorem evalQ_ge (c : ℚ) (cs : List ℚ) {s h : ℝ} (hs0 : 0 ≤ s) (hsh : s ≤ h) :
    (c : ℝ) - h * evalQ (cs.map (fun c => |c|)) h ≤ evalQ (c :: cs) s := by
  have h1 := abs_evalQ_le cs hs0 hsh
  have hA : 0 ≤ evalQ (cs.map (fun c => |c|)) h := (abs_nonneg _).trans h1
  have : |s * evalQ cs s| ≤ h * evalQ (cs.map (fun c => |c|)) h := by
    rw [abs_mul, abs_of_nonneg hs0]
    exact (mul_le_mul_of_nonneg_left h1 hs0).trans (mul_le_mul_of_nonneg_right hsh hA)
  simp only [evalQ]; linarith [neg_abs_le (s * evalQ cs s)]

/-- Crude upper bound: p(s) ≤ c₀ + h·Σ|cₖ₊₁|hᵏ on [0, h]. -/
theorem evalQ_le (c : ℚ) (cs : List ℚ) {s h : ℝ} (hs0 : 0 ≤ s) (hsh : s ≤ h) :
    evalQ (c :: cs) s ≤ (c : ℝ) + h * evalQ (cs.map (fun c => |c|)) h := by
  have h1 := abs_evalQ_le cs hs0 hsh
  have hA : 0 ≤ evalQ (cs.map (fun c => |c|)) h := (abs_nonneg _).trans h1
  have : |s * evalQ cs s| ≤ h * evalQ (cs.map (fun c => |c|)) h := by
    rw [abs_mul, abs_of_nonneg hs0]
    exact (mul_le_mul_of_nonneg_left h1 hs0).trans (mul_le_mul_of_nonneg_right hsh hA)
  simp only [evalQ]; linarith [le_abs_self (s * evalQ cs s)]

theorem evalQ_zero (c : ℚ) (cs : List ℚ) : evalQ (c :: cs) 0 = c := by simp [evalQ]

/-- Grönwall bound over a cell of length `h`, by `exp x < 1/(1 − x)` for 0 < x < 1. -/
theorem gronwallBound_le_cell {δ K ε x h : ℝ} (hδ : 0 ≤ δ) (hε : 0 ≤ ε) (hK : 0 < K)
    (hxh : x ≤ h) (hh : 0 < h) (hKh : K * h < 1) :
    gronwallBound δ K ε x ≤ δ * (1 / (1 - K * h)) + ε / K * (1 / (1 - K * h) - 1) := by
  rw [gronwallBound_of_K_ne_0 hK.ne']
  have he : Real.exp (K * x) ≤ 1 / (1 - K * h) :=
    (Real.exp_le_exp.2 (by nlinarith)).trans
      (Real.exp_bound_div_one_sub_of_interval' (by positivity) hKh).le
  have hεK : 0 ≤ ε / K := div_nonneg hε hK.le
  simp only
  gcongr

end Checked.Sim
