import Mathlib
import Checked.Records.Basic

/-!
# Chemistry (THE RESULT part 5): the critical point of the cubic equations of state

**Question.** Every process simulator computes phase behaviour with a cubic equation of state
(van der Waals 1873, Redlich–Kwong 1949, Soave 1972, Peng–Robinson 1976). Their parameters are
fixed from the critical point through the universal constants Ω_a, Ω_b, Z_c (printed, e.g.,
as `a = 0.45724 R²T_c²/P_c`, `b = 0.07780 R T_c/P_c`, `Z_c = 0.307` for Peng–Robinson). These
constants are derived by hand in every textbook from the conditions (∂P/∂v)_T = (∂²P/∂v²)_T = 0,
assuming tacitly that the critical point exists and is unique.

**What is stated here** for the generalized two-parameter family
`P(T, v) = R T/(v − b) − a/(v² + u b v + w b²)`
(van der Waals: u = w = 0; Redlich–Kwong and Soave–Redlich–Kwong: u = 1, w = 0;
Peng–Robinson: u = 2, w = −1):
1. `isCritical_iff`: at fixed T > 0, a volume v > b is a critical point of the isotherm iff
   `v³ − 3bv² − 3(u+w)b²v − (u² + uw − w)b³ = 0` and `R T (v² + ubv + wb²)² = a (v−b)²(2v+ub)`.
2. `critCubic_existsUnique`: for u > −2 and 1 + u + w > 0 that cubic (in x = v/b) has exactly
   one root x > 1.
3. `exists_unique_critical`: for u > −2 and v² + ubv + wb² > 0 for all v ≥ b, every isotherm
   family with constant a, b > 0 has exactly one critical point (T, v) with T > 0, v > b.
4. `vdW_constants`, `rk_constants`, `pr_constants`: at *every* critical point (T, v)
   of the respective equation, Z_c, Ω_b, Ω_a round to the printed constants
   (vdW 3/8, 1/8, 27/64; RK/SRK 0.33333, 0.08664, 0.42748; PR 0.3074, 0.07780, 0.45724).
   `a` is the value a(T) at the temperature considered, so these hold for every temperature
   function α(T) (RK's T^{-1/2}, Soave's and Peng–Robinson's α(T; ω)) with Ω_a defined by
   a(T_c) = Ω_a R²T_c²/P_c.

Conventions: molar volume v, temperature T, gas constant R > 0, co-volume b > 0, attraction
parameter a > 0; reduced constants `Z_c = P v/(R T)`, `Ω_b = b P/(R T)`, `Ω_a = a P/(R T)²`
evaluated at the critical point. Derivatives are Mathlib's `deriv` in v at fixed T.

FROZEN (annex 40.1) in run 2026-10-31T0628Z before proof work.
-/

namespace Checked.Chemistry.CubicEOS

open Checked.Records

/-- Generalized two-parameter cubic equation of state: pressure at temperature `T` and molar
volume `v`, `P = R T/(v − b) − a/(v² + u b v + w b²)`. -/
noncomputable def cubicP (R a b u w T v : ℝ) : ℝ := R * T / (v - b) - a / (v ^ 2 + u * b * v + w * b ^ 2)

/-- Critical point of an isotherm `p` (pressure as a function of molar volume at fixed
temperature): zero slope and zero curvature, (∂P/∂v)_T = 0 and (∂²P/∂v²)_T = 0. -/
def IsCriticalIsotherm (p : ℝ → ℝ) (v : ℝ) : Prop := deriv p v = 0 ∧ deriv (deriv p) v = 0

/-- The critical cubic in `x = v_c/b`. -/
def critCubic (u w x : ℝ) : ℝ := x ^ 3 - 3 * x ^ 2 - 3 * (u + w) * x - (u ^ 2 + u * w - w)

/-- Critical-point conditions of the generalized cubic EOS, in closed form. -/
theorem isCritical_iff (R a b u w T v : ℝ) (hR : 0 < R) (ha : 0 < a) (hb : 0 < b) (hT : 0 < T)
    (hv : b < v) (hD : 0 < v ^ 2 + u * b * v + w * b ^ 2) :
    IsCriticalIsotherm (cubicP R a b u w T) v ↔
      (v ^ 3 - 3 * b * v ^ 2 - 3 * (u + w) * b ^ 2 * v - (u ^ 2 + u * w - w) * b ^ 3 = 0 ∧
        R * T * (v ^ 2 + u * b * v + w * b ^ 2) ^ 2 = a * (v - b) ^ 2 * (2 * v + u * b)) := by
  sorry

/-- The critical cubic has exactly one root above 1 (x = v_c/b > 1). -/
theorem critCubic_existsUnique (u w : ℝ) (hu : -2 < u) (h1 : 0 < 1 + u + w) :
    ∃! x : ℝ, 1 < x ∧ critCubic u w x = 0 := by
  sorry

/-- Existence and uniqueness of the critical point (T, v) of the generalized cubic EOS. -/
theorem exists_unique_critical (R a b u w : ℝ) (hR : 0 < R) (ha : 0 < a) (hb : 0 < b)
    (hu : -2 < u) (hD : ∀ v : ℝ, b ≤ v → 0 < v ^ 2 + u * b * v + w * b ^ 2) :
    ∃! p : ℝ × ℝ, 0 < p.1 ∧ b < p.2 ∧ IsCriticalIsotherm (cubicP R a b u w p.1) p.2 := by
  sorry

/-- van der Waals: at every critical point, Z_c = 3/8, Ω_b = 1/8, Ω_a = 27/64 (exactly). -/
theorem vdW_constants (R a b T v : ℝ) (hR : 0 < R) (ha : 0 < a) (hb : 0 < b) (hT : 0 < T)
    (hv : b < v) (hc : IsCriticalIsotherm (cubicP R a b 0 0 T) v) :
    cubicP R a b 0 0 T v * v / (R * T) = 3 / 8 ∧ b * cubicP R a b 0 0 T v / (R * T) = 1 / 8 ∧
      a * cubicP R a b 0 0 T v / (R * T) ^ 2 = 27 / 64 := by
  sorry

/-- Redlich–Kwong / Soave–Redlich–Kwong: at every critical point, Z_c = 1/3 exactly,
Ω_b = 0.08664 and Ω_a = 0.42748 to five decimals. -/
theorem rk_constants (R a b T v : ℝ) (hR : 0 < R) (ha : 0 < a) (hb : 0 < b) (hT : 0 < T)
    (hv : b < v) (hc : IsCriticalIsotherm (cubicP R a b 1 0 T) v) :
    cubicP R a b 1 0 T v * v / (R * T) = 1 / 3 ∧
      RoundsTo (b * cubicP R a b 1 0 T v / (R * T)) 0.08664 5 ∧
      RoundsTo (a * cubicP R a b 1 0 T v / (R * T) ^ 2) 0.42748 5 := by
  sorry

/-- Peng–Robinson: at every critical point, Z_c = 0.3074 (four decimals), Ω_b = 0.07780 and
Ω_a = 0.45724 (five decimals). -/
theorem pr_constants (R a b T v : ℝ) (hR : 0 < R) (ha : 0 < a) (hb : 0 < b) (hT : 0 < T)
    (hv : b < v) (hc : IsCriticalIsotherm (cubicP R a b 2 (-1) T) v) :
    RoundsTo (cubicP R a b 2 (-1) T v * v / (R * T)) 0.3074 4 ∧
      RoundsTo (b * cubicP R a b 2 (-1) T v / (R * T)) 0.07780 5 ∧
      RoundsTo (a * cubicP R a b 2 (-1) T v / (R * T) ^ 2) 0.45724 5 := by
  sorry

end Checked.Chemistry.CubicEOS
