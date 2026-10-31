import Mathlib
import Checked.Records.Basic

/-!
# Blind restatement: vdW liquid–vapour coexistence at T = 0.7 T_c and the vdW acentric factor

Written from the textbook claims alone (Maxwell equal-area construction; Pitzer's ω).
All proofs are `sorry`.
-/

namespace Blind.Coexistence
open Checked.Records

/-- van der Waals pressure `P(v,T) = R T/(v − b) − a/v²`. -/
noncomputable def vdwP (R a b T v : ℝ) : ℝ := R * T / (v - b) - a / v ^ 2

/-- Critical temperature `T_c = 8a/(27 R b)`. -/
noncomputable def Tc (R a b : ℝ) : ℝ := 8 * a / (27 * R * b)

/-- Critical pressure `P_c = a/(27 b²)`. -/
noncomputable def Pc (a b : ℝ) : ℝ := a / (27 * b ^ 2)

/-- Critical molar volume `v_c = 3b` (recorded for completeness). -/
def vc (b : ℝ) : ℝ := 3 * b

/-- Molar Gibbs energy of the vdW fluid along an isotherm, up to an additive function of `T`
alone (which cancels in comparisons at fixed `T`):
`g(v) = A(v) + P(v) v` with Helmholtz energy `A(v) = −R T log(v − b) − a/v (+ f(T))`.
Only used for `v > b > 0`, where `log` has a positive argument and `v ≠ 0`. -/
noncomputable def gibbs (R a b T v : ℝ) : ℝ :=
  -(R * T) * Real.log (v - b) - a / v + v * vdwP R a b T v

/-- Maxwell coexistence state at temperature `T`: liquid and gas molar volumes `b < v_l < v_g`
at a common pressure `p_s` (mechanical equilibrium) with equal molar Gibbs energy
(chemical equilibrium). The strict inequality `v_l < v_g` excludes the trivial "pair" of one
phase with itself. -/
def IsCoexistence (R a b T vl vg ps : ℝ) : Prop :=
  b < vl ∧ vl < vg ∧ vdwP R a b T vl = ps ∧ vdwP R a b T vg = ps ∧
    gibbs R a b T vl = gibbs R a b T vg

/-- Pitzer's acentric factor from the saturation pressure at `0.7 T_c`:
`ω = −log₁₀(p_s/P_c) − 1`. (Applied only where `p_s/P_c > 0` is part of the statement.) -/
noncomputable def acentric (a b ps : ℝ) : ℝ := -Real.logb 10 (ps / Pc a b) - 1

/-- Sanity statement for the modelling choice: for `b < v_l < v_g` at common pressure `p_s`,
equal Gibbs energy is the same as Maxwell's equal-area rule
`∫_{v_l}^{v_g} P dv = p_s (v_g − v_l)` (the integrand is continuous on `[v_l, v_g]`, so the
integral is a genuine one, not a junk value). -/
theorem equalGibbs_iff_equalArea (R a b T vl vg ps : ℝ) (hR : 0 < R) (ha : 0 < a) (hb : 0 < b)
    (hT : 0 < T) (hl : b < vl) (hlg : vl < vg)
    (hpl : vdwP R a b T vl = ps) (hpg : vdwP R a b T vg = ps) :
    gibbs R a b T vl = gibbs R a b T vg ↔
      ∫ v in vl..vg, vdwP R a b T v = ps * (vg - vl) := by
  sorry

/-- Claim 1 (existence): at `T = 0.7 T_c` a coexistence state exists; its reduced saturation
pressure `p_s/P_c` is 0.20046 to 5 decimals, `p_s > 0`, and the acentric factor of the vdW fluid
is −0.3020 to 4 decimals. -/
theorem coexistence_exists (R a b : ℝ) (hR : 0 < R) (ha : 0 < a) (hb : 0 < b) :
    ∃ vl vg ps : ℝ, IsCoexistence R a b (7 / 10 * Tc R a b) vl vg ps ∧
      0 < ps ∧
      RoundsTo (ps / Pc a b) 0.20046 5 ∧
      RoundsTo (acentric a b ps) (-0.3020) 4 := by
  sorry

/-- Claim 2 (uniqueness of the saturation pressure): every coexistence state at `T = 0.7 T_c`
has `p_s/P_c` equal to 0.20046 to 5 decimals. -/
theorem coexistence_unique (R a b : ℝ) (hR : 0 < R) (ha : 0 < a) (hb : 0 < b)
    (vl vg ps : ℝ) (h : IsCoexistence R a b (7 / 10 * Tc R a b) vl vg ps) :
    RoundsTo (ps / Pc a b) 0.20046 5 := by
  sorry

/-- Supplement (makes "the acentric factor of the vdW fluid" well defined): every coexistence
state at `T = 0.7 T_c` has positive saturation pressure and gives ω = −0.3020 to 4 decimals. -/
theorem acentric_unique (R a b : ℝ) (hR : 0 < R) (ha : 0 < a) (hb : 0 < b)
    (vl vg ps : ℝ) (h : IsCoexistence R a b (7 / 10 * Tc R a b) vl vg ps) :
    0 < ps ∧ RoundsTo (acentric a b ps) (-0.3020) 4 := by
  sorry

end Blind.Coexistence
