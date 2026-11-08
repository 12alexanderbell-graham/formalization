import Mathlib
import Work.FalknerSkan.MonotoneWindow

/-!
# Monotone-window theorems: the blind restatement, closed (run 2026-11-08T1028Z)

The two theorems below are the blind restater's statements (Sonnet, from the claim in words only;
`runs/2026-11-08T1028Z/blind/MWBlind.lean`), copied verbatim with their placeholder proofs replaced by proofs from
the program's frozen `Work.FalknerSkan.MonotoneWindow.hiemenz_monotone_window` and
`homann_monotone_window`. The blind version names the third derivative separately and states the
equation pointwise; the numbers are written as fractions.
-/

namespace Blind.MonotoneWindow

open Set Filter Topology

/-- Hiemenz flow: `f, f1, f2, f3` stand for `f, f', f'', f'''`, with one-sided derivatives
(within `[0,∞)`) at every point of `[0,∞)`; ODE `f''' + f f'' + 1 - (f')² = 0` there;
`f(0)=0`, `f'(0)=0`, `f' → 1`; if `f'' > 0` on `[0,∞)` then `f''(0)` lies in the open window. -/
theorem hiemenz_blind (f f1 f2 f3 : ℝ → ℝ)
    (h0 : ∀ x ∈ Ici (0:ℝ), HasDerivWithinAt f (f1 x) (Ici 0) x)
    (h1 : ∀ x ∈ Ici (0:ℝ), HasDerivWithinAt f1 (f2 x) (Ici 0) x)
    (h2 : ∀ x ∈ Ici (0:ℝ), HasDerivWithinAt f2 (f3 x) (Ici 0) x)
    (ode : ∀ x ∈ Ici (0:ℝ), f3 x + f x * f2 x + 1 - (f1 x) ^ 2 = 0)
    (bc0 : f 0 = 0) (bc1 : f1 0 = 0)
    (binf : Tendsto f1 atTop (𝓝 1))
    (pos : ∀ x ∈ Ici (0:ℝ), 0 < f2 x) :
    (12325876568 / 10 ^ 10 : ℝ) < f2 0 ∧ f2 0 < (12325876569 / 10 ^ 10 : ℝ) := by
  have hq : ∀ x ∈ Ici (0 : ℝ), HasDerivWithinAt f2 (-(f x * f2 x) - 1 + f1 x ^ 2) (Ici 0) x :=
    fun x hx => (h2 x hx).congr_deriv (by linarith [ode x hx])
  have h := Work.FalknerSkan.MonotoneWindow.hiemenz_monotone_window f f1 f2 h0 h1 hq bc0 bc1 binf pos
  constructor <;> norm_num <;> linarith [h.1, h.2]

/-- Homann flow: same setting with ODE `f''' + 2 f f'' + 1 - (f')² = 0`. -/
theorem homann_blind (f f1 f2 f3 : ℝ → ℝ)
    (h0 : ∀ x ∈ Ici (0:ℝ), HasDerivWithinAt f (f1 x) (Ici 0) x)
    (h1 : ∀ x ∈ Ici (0:ℝ), HasDerivWithinAt f1 (f2 x) (Ici 0) x)
    (h2 : ∀ x ∈ Ici (0:ℝ), HasDerivWithinAt f2 (f3 x) (Ici 0) x)
    (ode : ∀ x ∈ Ici (0:ℝ), f3 x + 2 * f x * f2 x + 1 - (f1 x) ^ 2 = 0)
    (bc0 : f 0 = 0) (bc1 : f1 0 = 0)
    (binf : Tendsto f1 atTop (𝓝 1))
    (pos : ∀ x ∈ Ici (0:ℝ), 0 < f2 x) :
    (13119376938 / 10 ^ 10 : ℝ) < f2 0 ∧ f2 0 < (13119376939 / 10 ^ 10 : ℝ) := by
  have hq : ∀ x ∈ Ici (0 : ℝ), HasDerivWithinAt f2 (-(2 * f x * f2 x) - 1 + f1 x ^ 2) (Ici 0) x :=
    fun x hx => (h2 x hx).congr_deriv (by linarith [ode x hx])
  have h := Work.FalknerSkan.MonotoneWindow.homann_monotone_window f f1 f2 h0 h1 hq bc0 bc1 binf pos
  constructor <;> norm_num <;> linarith [h.1, h.2]

end Blind.MonotoneWindow
