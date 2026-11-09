import Mathlib
import Work.FalknerSkan.Unrestricted

/-!
# Falkner–Skan and stagnation-point problems with no bound on f': the blind restatement, closed (run 2026-11-09T0028Z)

The nine theorems are the blind restater's text (Sonnet, from the claims in words only;
`runs/2026-11-09T0028Z/blind/UnrestrictedBlind.lean`), copied verbatim with their placeholder proofs
replaced by proofs from the program's `Work.FalknerSkan.Unrestricted` headlines.
-/

namespace Blind.Unrestricted

/-- Solutions: `f, f', f'', f'''` given as explicit functions; derivatives are one-sided
on `Ici 0`; the ODE is required for all `x ≥ 0`. -/

theorem positivity (β : ℝ) (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    (f f1 f2 f3 : ℝ → ℝ)
    (h1 : ∀ x, 0 ≤ x → HasDerivWithinAt f (f1 x) (Set.Ici 0) x)
    (h2 : ∀ x, 0 ≤ x → HasDerivWithinAt f1 (f2 x) (Set.Ici 0) x)
    (h3 : ∀ x, 0 ≤ x → HasDerivWithinAt f2 (f3 x) (Set.Ici 0) x)
    (ode : ∀ x, 0 ≤ x → f3 x + 1 * f x * f2 x + β * (1 - f1 x ^ 2) = 0)
    (bc0 : f 0 = 0)
    (bc1 : f1 0 = 0)
    (bc2 : Filter.Tendsto f1 Filter.atTop (nhds 1)) :
    ∀ x, 0 ≤ x → 0 < f2 x := by
  exact Work.FalknerSkan.Unrestricted.fs_monotone_of_limit β hβ0 hβ1 f f1 f2 h1 h2 (fun x hx => (h3 x hx).congr_deriv (by linear_combination ode x hx)) bc0 bc1 bc2

theorem hiemenz_value
    (f f1 f2 f3 : ℝ → ℝ)
    (h1 : ∀ x, 0 ≤ x → HasDerivWithinAt f (f1 x) (Set.Ici 0) x)
    (h2 : ∀ x, 0 ≤ x → HasDerivWithinAt f1 (f2 x) (Set.Ici 0) x)
    (h3 : ∀ x, 0 ≤ x → HasDerivWithinAt f2 (f3 x) (Set.Ici 0) x)
    (ode : ∀ x, 0 ≤ x → f3 x + (1 : ℝ) * f x * f2 x + (1 : ℝ) * (1 - f1 x ^ 2) = 0)
    (bc0 : f 0 = 0)
    (bc1 : f1 0 = 0)
    (bc2 : Filter.Tendsto f1 Filter.atTop (nhds 1)) :
    (1.2325876568 : ℝ) < f2 0 ∧ f2 0 < 1.2325876569 := by
  exact Work.FalknerSkan.Unrestricted.hiemenz_limit_window f f1 f2 h1 h2 (fun x hx => (h3 x hx).congr_deriv (by linear_combination ode x hx)) bc0 bc1 bc2

theorem hiemenz_unique
    (f f1 f2 f3 : ℝ → ℝ)
    (h1 : ∀ x, 0 ≤ x → HasDerivWithinAt f (f1 x) (Set.Ici 0) x)
    (h2 : ∀ x, 0 ≤ x → HasDerivWithinAt f1 (f2 x) (Set.Ici 0) x)
    (h3 : ∀ x, 0 ≤ x → HasDerivWithinAt f2 (f3 x) (Set.Ici 0) x)
    (ode : ∀ x, 0 ≤ x → f3 x + (1 : ℝ) * f x * f2 x + (1 : ℝ) * (1 - f1 x ^ 2) = 0)
    (bc0 : f 0 = 0)
    (bc1 : f1 0 = 0)
    (bc2 : Filter.Tendsto f1 Filter.atTop (nhds 1))
    (f' f1' f2' f3' : ℝ → ℝ)
    (h1' : ∀ x, 0 ≤ x → HasDerivWithinAt f' (f1' x) (Set.Ici 0) x)
    (h2' : ∀ x, 0 ≤ x → HasDerivWithinAt f1' (f2' x) (Set.Ici 0) x)
    (h3' : ∀ x, 0 ≤ x → HasDerivWithinAt f2' (f3' x) (Set.Ici 0) x)
    (ode' : ∀ x, 0 ≤ x → f3' x + (1 : ℝ) * f' x * f2' x + (1 : ℝ) * (1 - f1' x ^ 2) = 0)
    (bc0' : f' 0 = 0)
    (bc1' : f1' 0 = 0)
    (bc2' : Filter.Tendsto f1' Filter.atTop (nhds 1)) :
    ∀ x, 0 ≤ x → f x = f' x ∧ f1 x = f1' x ∧ f2 x = f2' x := by
  exact Work.FalknerSkan.Unrestricted.hiemenz_limit_equal f f1 f2 f' f1' f2' h1 h2 (fun x hx => (h3 x hx).congr_deriv (by linear_combination ode x hx)) bc0 bc1 bc2
    h1' h2' (fun x hx => (h3' x hx).congr_deriv (by linear_combination ode' x hx)) bc0' bc1' bc2'

theorem homann_value
    (f f1 f2 f3 : ℝ → ℝ)
    (h1 : ∀ x, 0 ≤ x → HasDerivWithinAt f (f1 x) (Set.Ici 0) x)
    (h2 : ∀ x, 0 ≤ x → HasDerivWithinAt f1 (f2 x) (Set.Ici 0) x)
    (h3 : ∀ x, 0 ≤ x → HasDerivWithinAt f2 (f3 x) (Set.Ici 0) x)
    (ode : ∀ x, 0 ≤ x → f3 x + (2 : ℝ) * f x * f2 x + (1 : ℝ) * (1 - f1 x ^ 2) = 0)
    (bc0 : f 0 = 0)
    (bc1 : f1 0 = 0)
    (bc2 : Filter.Tendsto f1 Filter.atTop (nhds 1)) :
    (1.3119376938 : ℝ) < f2 0 ∧ f2 0 < 1.3119376939 := by
  exact Work.FalknerSkan.Unrestricted.homann_limit_window f f1 f2 h1 h2 (fun x hx => (h3 x hx).congr_deriv (by linear_combination ode x hx)) bc0 bc1 bc2

theorem homann_unique
    (f f1 f2 f3 : ℝ → ℝ)
    (h1 : ∀ x, 0 ≤ x → HasDerivWithinAt f (f1 x) (Set.Ici 0) x)
    (h2 : ∀ x, 0 ≤ x → HasDerivWithinAt f1 (f2 x) (Set.Ici 0) x)
    (h3 : ∀ x, 0 ≤ x → HasDerivWithinAt f2 (f3 x) (Set.Ici 0) x)
    (ode : ∀ x, 0 ≤ x → f3 x + (2 : ℝ) * f x * f2 x + (1 : ℝ) * (1 - f1 x ^ 2) = 0)
    (bc0 : f 0 = 0)
    (bc1 : f1 0 = 0)
    (bc2 : Filter.Tendsto f1 Filter.atTop (nhds 1))
    (f' f1' f2' f3' : ℝ → ℝ)
    (h1' : ∀ x, 0 ≤ x → HasDerivWithinAt f' (f1' x) (Set.Ici 0) x)
    (h2' : ∀ x, 0 ≤ x → HasDerivWithinAt f1' (f2' x) (Set.Ici 0) x)
    (h3' : ∀ x, 0 ≤ x → HasDerivWithinAt f2' (f3' x) (Set.Ici 0) x)
    (ode' : ∀ x, 0 ≤ x → f3' x + (2 : ℝ) * f' x * f2' x + (1 : ℝ) * (1 - f1' x ^ 2) = 0)
    (bc0' : f' 0 = 0)
    (bc1' : f1' 0 = 0)
    (bc2' : Filter.Tendsto f1' Filter.atTop (nhds 1)) :
    ∀ x, 0 ≤ x → f x = f' x ∧ f1 x = f1' x ∧ f2 x = f2' x := by
  exact Work.FalknerSkan.Unrestricted.homann_limit_equal f f1 f2 f' f1' f2' h1 h2 (fun x hx => (h3 x hx).congr_deriv (by linear_combination ode x hx)) bc0 bc1 bc2
    h1' h2' (fun x hx => (h3' x hx).congr_deriv (by linear_combination ode' x hx)) bc0' bc1' bc2'

theorem fs_half_value
    (f f1 f2 f3 : ℝ → ℝ)
    (h1 : ∀ x, 0 ≤ x → HasDerivWithinAt f (f1 x) (Set.Ici 0) x)
    (h2 : ∀ x, 0 ≤ x → HasDerivWithinAt f1 (f2 x) (Set.Ici 0) x)
    (h3 : ∀ x, 0 ≤ x → HasDerivWithinAt f2 (f3 x) (Set.Ici 0) x)
    (ode : ∀ x, 0 ≤ x → f3 x + (1 : ℝ) * f x * f2 x + (1/2 : ℝ) * (1 - f1 x ^ 2) = 0)
    (bc0 : f 0 = 0)
    (bc1 : f1 0 = 0)
    (bc2 : Filter.Tendsto f1 Filter.atTop (nhds 1)) :
    (0.927680039 : ℝ) < f2 0 ∧ f2 0 < 0.927680040 := by
  exact Work.FalknerSkan.Unrestricted.fs_half_limit_window f f1 f2 h1 h2 (fun x hx => (h3 x hx).congr_deriv (by linear_combination ode x hx)) bc0 bc1 bc2

theorem fs_half_unique
    (f f1 f2 f3 : ℝ → ℝ)
    (h1 : ∀ x, 0 ≤ x → HasDerivWithinAt f (f1 x) (Set.Ici 0) x)
    (h2 : ∀ x, 0 ≤ x → HasDerivWithinAt f1 (f2 x) (Set.Ici 0) x)
    (h3 : ∀ x, 0 ≤ x → HasDerivWithinAt f2 (f3 x) (Set.Ici 0) x)
    (ode : ∀ x, 0 ≤ x → f3 x + (1 : ℝ) * f x * f2 x + (1/2 : ℝ) * (1 - f1 x ^ 2) = 0)
    (bc0 : f 0 = 0)
    (bc1 : f1 0 = 0)
    (bc2 : Filter.Tendsto f1 Filter.atTop (nhds 1))
    (f' f1' f2' f3' : ℝ → ℝ)
    (h1' : ∀ x, 0 ≤ x → HasDerivWithinAt f' (f1' x) (Set.Ici 0) x)
    (h2' : ∀ x, 0 ≤ x → HasDerivWithinAt f1' (f2' x) (Set.Ici 0) x)
    (h3' : ∀ x, 0 ≤ x → HasDerivWithinAt f2' (f3' x) (Set.Ici 0) x)
    (ode' : ∀ x, 0 ≤ x → f3' x + (1 : ℝ) * f' x * f2' x + (1/2 : ℝ) * (1 - f1' x ^ 2) = 0)
    (bc0' : f' 0 = 0)
    (bc1' : f1' 0 = 0)
    (bc2' : Filter.Tendsto f1' Filter.atTop (nhds 1)) :
    ∀ x, 0 ≤ x → f x = f' x ∧ f1 x = f1' x ∧ f2 x = f2' x := by
  exact Work.FalknerSkan.Unrestricted.fs_half_limit_equal f f1 f2 f' f1' f2' h1 h2 (fun x hx => (h3 x hx).congr_deriv (by linear_combination ode x hx)) bc0 bc1 bc2
    h1' h2' (fun x hx => (h3' x hx).congr_deriv (by linear_combination ode' x hx)) bc0' bc1' bc2'

theorem fs_fifth_value
    (f f1 f2 f3 : ℝ → ℝ)
    (h1 : ∀ x, 0 ≤ x → HasDerivWithinAt f (f1 x) (Set.Ici 0) x)
    (h2 : ∀ x, 0 ≤ x → HasDerivWithinAt f1 (f2 x) (Set.Ici 0) x)
    (h3 : ∀ x, 0 ≤ x → HasDerivWithinAt f2 (f3 x) (Set.Ici 0) x)
    (ode : ∀ x, 0 ≤ x → f3 x + (1 : ℝ) * f x * f2 x + (1/5 : ℝ) * (1 - f1 x ^ 2) = 0)
    (bc0 : f 0 = 0)
    (bc1 : f1 0 = 0)
    (bc2 : Filter.Tendsto f1 Filter.atTop (nhds 1)) :
    (0.6867081809 : ℝ) < f2 0 ∧ f2 0 < 0.6867081811 := by
  exact Work.FalknerSkan.Unrestricted.fs_fifth_limit_window f f1 f2 h1 h2 (fun x hx => (h3 x hx).congr_deriv (by linear_combination ode x hx)) bc0 bc1 bc2

theorem fs_fifth_unique
    (f f1 f2 f3 : ℝ → ℝ)
    (h1 : ∀ x, 0 ≤ x → HasDerivWithinAt f (f1 x) (Set.Ici 0) x)
    (h2 : ∀ x, 0 ≤ x → HasDerivWithinAt f1 (f2 x) (Set.Ici 0) x)
    (h3 : ∀ x, 0 ≤ x → HasDerivWithinAt f2 (f3 x) (Set.Ici 0) x)
    (ode : ∀ x, 0 ≤ x → f3 x + (1 : ℝ) * f x * f2 x + (1/5 : ℝ) * (1 - f1 x ^ 2) = 0)
    (bc0 : f 0 = 0)
    (bc1 : f1 0 = 0)
    (bc2 : Filter.Tendsto f1 Filter.atTop (nhds 1))
    (f' f1' f2' f3' : ℝ → ℝ)
    (h1' : ∀ x, 0 ≤ x → HasDerivWithinAt f' (f1' x) (Set.Ici 0) x)
    (h2' : ∀ x, 0 ≤ x → HasDerivWithinAt f1' (f2' x) (Set.Ici 0) x)
    (h3' : ∀ x, 0 ≤ x → HasDerivWithinAt f2' (f3' x) (Set.Ici 0) x)
    (ode' : ∀ x, 0 ≤ x → f3' x + (1 : ℝ) * f' x * f2' x + (1/5 : ℝ) * (1 - f1' x ^ 2) = 0)
    (bc0' : f' 0 = 0)
    (bc1' : f1' 0 = 0)
    (bc2' : Filter.Tendsto f1' Filter.atTop (nhds 1)) :
    ∀ x, 0 ≤ x → f x = f' x ∧ f1 x = f1' x ∧ f2 x = f2' x := by
  exact Work.FalknerSkan.Unrestricted.fs_fifth_limit_equal f f1 f2 f' f1' f2' h1 h2 (fun x hx => (h3 x hx).congr_deriv (by linear_combination ode x hx)) bc0 bc1 bc2
    h1' h2' (fun x hx => (h3' x hx).congr_deriv (by linear_combination ode' x hx)) bc0' bc1' bc2'

end Blind.Unrestricted
