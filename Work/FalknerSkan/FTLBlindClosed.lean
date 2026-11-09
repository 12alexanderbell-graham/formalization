import Mathlib
import Checked.FalknerSkan.LimitTenth

/-!
# Falkner–Skan β = 1/10 with no bound on f': the blind restatement, closed (run 2026-11-09T0428Z)

The structure `IsSolution` and the two theorems are the blind restater's text (Sonnet, from the claims in
words only; `runs/2026-11-09T0428Z/blind/FSTenthLimitBlind.lean`), copied verbatim with their placeholder
proofs replaced by proofs from the program's `Checked.FalknerSkan.LimitTenth` headlines.
-/

namespace Blind.FSTenthLimit

/-- `f, f1, f2, f3` stand for `f, f', f'', f'''`: derivatives are taken within `[0,∞)`
at every `η ≥ 0`, the Falkner–Skan ODE with `β = 1/10` holds at every `η ≥ 0`,
`f(0) = 0`, `f'(0) = 0` and `f'(η) → 1` as `η → ∞`. -/
def IsSolution (f f1 f2 f3 : ℝ → ℝ) : Prop :=
  (∀ x : ℝ, 0 ≤ x → HasDerivWithinAt f (f1 x) (Set.Ici 0) x) ∧
  (∀ x : ℝ, 0 ≤ x → HasDerivWithinAt f1 (f2 x) (Set.Ici 0) x) ∧
  (∀ x : ℝ, 0 ≤ x → HasDerivWithinAt f2 (f3 x) (Set.Ici 0) x) ∧
  (∀ x : ℝ, 0 ≤ x → f3 x + f x * f2 x + (1 / 10 : ℝ) * (1 - f1 x ^ 2) = 0) ∧
  f 0 = 0 ∧ f1 0 = 0 ∧
  Filter.Tendsto f1 Filter.atTop (nhds 1)

theorem toSys {f f1 f2 f3 : ℝ → ℝ} (h : IsSolution f f1 f2 f3) :
    ∀ η ∈ Set.Ici (0 : ℝ), HasDerivWithinAt f2 (-(f η * f2 η) - 1 / 10 * (1 - f1 η ^ 2)) (Set.Ici 0) η :=
  fun η hη => (h.2.2.1 η hη).congr_deriv (by linear_combination h.2.2.2.1 η hη)

/-- Claim 1: every solution has `0.5870352191 < f''(0) < 0.5870352193`. -/
theorem wall_shear_window (f f1 f2 f3 : ℝ → ℝ) (h : IsSolution f f1 f2 f3) :
    (5870352191 / 10000000000 : ℝ) < f2 0 ∧ f2 0 < (5870352193 / 10000000000 : ℝ) := by
  have W := Checked.FalknerSkan.LimitTenth.fs_tenth_limit_window f f1 f2 (fun η hη => h.1 η hη)
    (fun η hη => h.2.1 η hη) (toSys h) h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2
  constructor <;> [linarith [W.1]; linarith [W.2]]

/-- Claim 2: any two solutions agree (with first and second derivatives) for all `η ≥ 0`. -/
theorem solution_unique (f f1 f2 f3 g g1 g2 g3 : ℝ → ℝ)
    (hf : IsSolution f f1 f2 f3) (hg : IsSolution g g1 g2 g3) :
    ∀ x : ℝ, 0 ≤ x → f x = g x ∧ f1 x = g1 x ∧ f2 x = g2 x := by
  intro x hx
  exact Checked.FalknerSkan.LimitTenth.fs_tenth_limit_equal f f1 f2 g g1 g2 (fun η hη => hf.1 η hη)
    (fun η hη => hf.2.1 η hη) (toSys hf) hf.2.2.2.2.1 hf.2.2.2.2.2.1 hf.2.2.2.2.2.2
    (fun η hη => hg.1 η hη) (fun η hη => hg.2.1 η hη) (toSys hg) hg.2.2.2.2.1 hg.2.2.2.2.2.1
    hg.2.2.2.2.2.2 x hx

#print axioms wall_shear_window
#print axioms solution_unique

end Blind.FSTenthLimit
