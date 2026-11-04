import Mathlib
import Checked.Records.Basic

/-!
# Redlich–Kwong fluid: reduced vapour pressure at `T = 0.7 T_c` and acentric factor (blind restatement)

Model: `P(v,T) = R T/(v - b) - A/(√T · v (v + b))`, with `R, A, b > 0`, considered on the
physical domain `v > b`, `T > 0` (all statements below only evaluate `P` there).

* Critical point: characterised by derivatives (`IsCriticalPoint`): `T_c > 0`, `v_c > b`,
  `∂P/∂v = 0`, `∂²P/∂v² = 0` at `(v_c, T_c)`, and `P_c = P(v_c, T_c)`.
  (For reference only, not used: solving these gives `v_c = b/(2^{1/3} - 1)`,
  `Z_c = P_c v_c/(R T_c) = 1/3`, `b = Ω_b R T_c/P_c` with `Ω_b = (2^{1/3}-1)/3`, and
  `A = Ω_a R² T_c^{5/2}/P_c` with `Ω_a = 1/(9(2^{1/3}-1))`.)
  Since `v_c > b > 0`, the function `v ↦ P(v,T_c)` is smooth on a neighbourhood of `v_c`, so
  Mathlib's `deriv` (and `deriv ∘ deriv`) at `v_c` are the genuine derivatives (no junk).
* Coexistence (Maxwell equal area) at temperature `T`: `b < v_l < v_g`, `P(v_l,T) = P(v_g,T) = p_s`,
  and `∫_{v_l}^{v_g} P(v,T) dv = p_s (v_g - v_l)`. The integrand is continuous on `[v_l, v_g]`.
* Acentric factor: `ω = -log₁₀(p_s/P_c) - 1`. The rounding conclusion `p_s/P_c ≈ 0.087`
  forces `p_s/P_c > 0`, so `Real.logb 10` is evaluated at a positive argument; we also state
  positivity explicitly.
* "To 3 decimals" is read as `|x - d| ≤ 1/(2·10³)` (`Checked.Records.RoundsTo x d 3`).
-/

namespace Blind.RKAcentric

open Real MeasureTheory intervalIntegral

/-- Redlich–Kwong pressure. Physically meaningful only for `v > b`, `T > 0`. -/
noncomputable def rkP (R A b : ℝ) (v T : ℝ) : ℝ :=
  R * T / (v - b) - A / (Real.sqrt T * v * (v + b))

/-- `(T_c, v_c, P_c)` is a critical point of the RK fluid: the isotherm at `T_c` has zero slope
and zero curvature in `v` at `v_c`, and `P_c` is the pressure there. -/
def IsCriticalPoint (R A b : ℝ) (Tc vc Pc : ℝ) : Prop :=
  0 < Tc ∧ b < vc ∧
  deriv (fun v => rkP R A b v Tc) vc = 0 ∧
  deriv (deriv (fun v => rkP R A b v Tc)) vc = 0 ∧
  Pc = rkP R A b vc Tc

/-- Vapour–liquid coexistence at temperature `T` by Maxwell's equal-area construction:
liquid volume `v_l` (above the co-volume `b`) below gas volume `v_g`, both at pressure `p_s`,
with equal areas. -/
def IsCoexistence (R A b : ℝ) (T vl vg ps : ℝ) : Prop :=
  b < vl ∧ vl < vg ∧
  rkP R A b vl T = ps ∧ rkP R A b vg T = ps ∧
  (∫ v in vl..vg, rkP R A b v T) = ps * (vg - vl)

/-- Pitzer's acentric factor from the saturation pressure at `0.7 T_c` and the critical
pressure. Used only where `ps / Pc > 0`. -/
noncomputable def acentric (ps Pc : ℝ) : ℝ :=
  -Real.logb 10 (ps / Pc) - 1

/-- Supporting statement (presupposed by "its critical point"): an RK critical point with
`v_c > b` exists for all `R, A, b > 0`. -/
theorem critical_point_exists (R A b : ℝ) (hR : 0 < R) (hA : 0 < A) (hb : 0 < b) :
    ∃ Tc vc Pc, IsCriticalPoint R A b Tc vc Pc := by
  sorry

/-- Supporting statement: the critical point is unique. -/
theorem critical_point_unique (R A b : ℝ) (hR : 0 < R) (hA : 0 < A) (hb : 0 < b)
    (Tc vc Pc Tc' vc' Pc' : ℝ)
    (h : IsCriticalPoint R A b Tc vc Pc) (h' : IsCriticalPoint R A b Tc' vc' Pc') :
    Tc = Tc' ∧ vc = vc' ∧ Pc = Pc' := by
  sorry

/-- Claim, part 1 (existence): at `T = 0.7 T_c` a coexistence state exists. -/
theorem coexistence_exists (R A b : ℝ) (hR : 0 < R) (hA : 0 < A) (hb : 0 < b)
    (Tc vc Pc : ℝ) (hc : IsCriticalPoint R A b Tc vc Pc) :
    ∃ vl vg ps, IsCoexistence R A b (7 / 10 * Tc) vl vg ps := by
  sorry

/-- Claim, part 2 (the numbers, for every coexistence state): every coexistence state at
`T = 0.7 T_c` has `p_s/P_c = 0.087` and `ω = 0.058`, each to 3 decimals. -/
theorem coexistence_numbers (R A b : ℝ) (hR : 0 < R) (hA : 0 < A) (hb : 0 < b)
    (Tc vc Pc : ℝ) (hc : IsCriticalPoint R A b Tc vc Pc)
    (vl vg ps : ℝ) (hco : IsCoexistence R A b (7 / 10 * Tc) vl vg ps) :
    0 < ps / Pc ∧
    Checked.Records.RoundsTo (ps / Pc) (87 / 1000) 3 ∧
    Checked.Records.RoundsTo (acentric ps Pc) (58 / 1000) 3 := by
  sorry

/-- The full claim as a single statement. -/
theorem rk_acentric (R A b : ℝ) (hR : 0 < R) (hA : 0 < A) (hb : 0 < b)
    (Tc vc Pc : ℝ) (hc : IsCriticalPoint R A b Tc vc Pc) :
    (∃ vl vg ps, IsCoexistence R A b (7 / 10 * Tc) vl vg ps) ∧
    ∀ vl vg ps, IsCoexistence R A b (7 / 10 * Tc) vl vg ps →
      0 < ps / Pc ∧
      Checked.Records.RoundsTo (ps / Pc) (87 / 1000) 3 ∧
      Checked.Records.RoundsTo (acentric ps Pc) (58 / 1000) 3 := by
  sorry

end Blind.RKAcentric
