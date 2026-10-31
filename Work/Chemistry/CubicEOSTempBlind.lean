import Mathlib

/-!
# Critical points of cubic equations of state (blind restatement)

* Redlich–Kwong (1949): `P(T, v) = R T / (v - b) - A / (√T · v (v + b))`.
* General two-parameter cubic family with temperature-dependent attraction:
  `P(T, v) = R T / (v - b) - a(T) / (v² + u b v + w b²)`.

A critical point `(T, v)` is a point where, along the isotherm at fixed `T`,
both `(∂P/∂v)_T` and `(∂²P/∂v²)_T` vanish.
-/

namespace Work.Chemistry.CubicEOSTempBlind

open Set

/-- Original Redlich–Kwong pressure with constants `R`, `A`, `b`. -/
noncomputable def rkPressure (R A b : ℝ) (T v : ℝ) : ℝ :=
  R * T / (v - b) - A / (Real.sqrt T * v * (v + b))

/-- General cubic pressure `R T/(v-b) - a(T)/(v² + u b v + w b²)`. -/
noncomputable def cubicPressure (R b u w : ℝ) (a : ℝ → ℝ) (T v : ℝ) : ℝ :=
  R * T / (v - b) - a T / (v ^ 2 + u * b * v + w * b ^ 2)

/-- `(T, v)` is a critical point of the equation of state `P` : on the isotherm
`v ↦ P T v`, the first and second derivatives with respect to `v` vanish at `v`. -/
def IsCriticalPoint (P : ℝ → ℝ → ℝ) (T v : ℝ) : Prop :=
  deriv (fun x => P T x) v = 0 ∧
    deriv (fun y => deriv (fun x => P T x) y) v = 0

/-- **Redlich–Kwong (1949).** With `R, A, b > 0`, there is exactly one critical
point `(T_c, v_c)` with `T_c > 0` and `v_c > b`. -/
theorem rk_existsUnique_critical (R A b : ℝ) (hR : 0 < R) (hA : 0 < A) (hb : 0 < b) :
    ∃! p : ℝ × ℝ, 0 < p.1 ∧ b < p.2 ∧ IsCriticalPoint (rkPressure R A b) p.1 p.2 := by
  sorry

/-- **General cubic EOS.** For `u > -2`, `1 + u + w > 0`, and an attraction function
`a` positive on `T > 0` such that `T ↦ T / a(T)` is strictly increasing on `(0, ∞)` and
takes every positive value there, there is exactly one critical point `(T_c, v_c)` with
`T_c > 0` and `v_c > b`. -/
theorem cubic_existsUnique_critical (R b u w : ℝ) (a : ℝ → ℝ)
    (hR : 0 < R) (hb : 0 < b) (hu : -2 < u) (huw : 0 < 1 + u + w)
    (ha_pos : ∀ T, 0 < T → 0 < a T)
    (ha_mono : StrictMonoOn (fun T => T / a T) (Ioi 0))
    (ha_surj : ∀ y, 0 < y → ∃ T, 0 < T ∧ T / a T = y) :
    ∃! p : ℝ × ℝ, 0 < p.1 ∧ b < p.2 ∧
      IsCriticalPoint (cubicPressure R b u w a) p.1 p.2 := by
  sorry

end Work.Chemistry.CubicEOSTempBlind
