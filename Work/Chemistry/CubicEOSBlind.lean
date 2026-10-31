import Mathlib

/-!
# Critical constants of the van der Waals, Redlich–Kwong and Peng–Robinson equations

Blind restatement (statements only, proofs `sorry`).

Conventions: `R a b > 0` are constants, `T` the temperature, `v` the molar volume.
For RK and PR, `a` denotes the attraction parameter evaluated at the temperature
considered (in particular at `T_c` in the critical-constant statements); since the
critical conditions are derivatives in `v` at fixed `T`, it enters as a constant.
-/

namespace Work.Chemistry.CubicEOSBlind

/-- van der Waals: `P = RT/(v-b) - a/v^2`. -/
noncomputable def vdWPressure (R a b T v : ℝ) : ℝ :=
  R * T / (v - b) - a / v ^ 2

/-- Redlich–Kwong: `P = RT/(v-b) - a/(v(v+b))`. -/
noncomputable def rkPressure (R a b T v : ℝ) : ℝ :=
  R * T / (v - b) - a / (v * (v + b))

/-- Peng–Robinson: `P = RT/(v-b) - a/(v(v+b) + b(v-b))`. -/
noncomputable def prPressure (R a b T v : ℝ) : ℝ :=
  R * T / (v - b) - a / (v * (v + b) + b * (v - b))

/-- `(T, v)` is a critical point of the isotherm family `P` (with covolume `b`):
physical domain `T > 0`, `v > b`, and on the isotherm through `T` the first and
second derivatives of `P` with respect to `v` (at fixed `T`) vanish at `v`. -/
def IsCriticalPoint (P : ℝ → ℝ → ℝ) (b T v : ℝ) : Prop :=
  0 < T ∧ b < v ∧ deriv (fun w => P T w) v = 0 ∧ deriv (deriv (fun w => P T w)) v = 0

/-- `x` rounds to `d` at `k` decimals. -/
def RoundsTo (x d : ℝ) (k : ℕ) : Prop :=
  |x - d| ≤ 1 / (2 * 10 ^ k)

/-! ## 1. Existence and uniqueness of the critical point -/

theorem vdW_critical_existsUnique (R a b : ℝ) (hR : 0 < R) (ha : 0 < a) (hb : 0 < b) :
    ∃! p : ℝ × ℝ, IsCriticalPoint (vdWPressure R a b) b p.1 p.2 := by
  sorry

theorem rk_critical_existsUnique (R a b : ℝ) (hR : 0 < R) (ha : 0 < a) (hb : 0 < b) :
    ∃! p : ℝ × ℝ, IsCriticalPoint (rkPressure R a b) b p.1 p.2 := by
  sorry

theorem pr_critical_existsUnique (R a b : ℝ) (hR : 0 < R) (ha : 0 < a) (hb : 0 < b) :
    ∃! p : ℝ × ℝ, IsCriticalPoint (prPressure R a b) b p.1 p.2 := by
  sorry

/-! ## 2. Reduced critical constants
`Z_c = P_c v_c/(R T_c)`, `Ω_b = b P_c/(R T_c)`, `Ω_a = a P_c/(R T_c)^2`,
with `P_c = P(T_c, v_c)`, for every critical point `(T_c, v_c)`. -/

theorem vdW_critical_constants (R a b : ℝ) (hR : 0 < R) (ha : 0 < a) (hb : 0 < b)
    (Tc vc : ℝ) (hc : IsCriticalPoint (vdWPressure R a b) b Tc vc) :
    vdWPressure R a b Tc vc * vc / (R * Tc) = 3 / 8 ∧
    b * vdWPressure R a b Tc vc / (R * Tc) = 1 / 8 ∧
    a * vdWPressure R a b Tc vc / (R * Tc) ^ 2 = 27 / 64 := by
  sorry

theorem rk_critical_constants (R a b : ℝ) (hR : 0 < R) (ha : 0 < a) (hb : 0 < b)
    (Tc vc : ℝ) (hc : IsCriticalPoint (rkPressure R a b) b Tc vc) :
    rkPressure R a b Tc vc * vc / (R * Tc) = 1 / 3 ∧
    RoundsTo (b * rkPressure R a b Tc vc / (R * Tc)) 0.08664 5 ∧
    RoundsTo (a * rkPressure R a b Tc vc / (R * Tc) ^ 2) 0.42748 5 := by
  sorry

theorem pr_critical_constants (R a b : ℝ) (hR : 0 < R) (ha : 0 < a) (hb : 0 < b)
    (Tc vc : ℝ) (hc : IsCriticalPoint (prPressure R a b) b Tc vc) :
    RoundsTo (prPressure R a b Tc vc * vc / (R * Tc)) 0.3074 4 ∧
    RoundsTo (b * prPressure R a b Tc vc / (R * Tc)) 0.07780 5 ∧
    RoundsTo (a * prPressure R a b Tc vc / (R * Tc) ^ 2) 0.45724 5 := by
  sorry

end Work.Chemistry.CubicEOSBlind
