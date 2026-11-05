import Mathlib
import Checked.Records.Basic

/-!
# Peng–Robinson fluid with Soave alpha, `ω = 1`: reduced vapour pressure at `0.7 T_c` (blind restatement)

`P(v,T) = R T/(v - b) - a(T)/(v² + 2 b v - b²)`, `a(T) = a_c (1 + κ (1 - √(T/T_c)))²`,
`κ = 0.37464 + 1.54226 ω - 0.26992 ω²` at `ω = 1`. Domain `v > b`, `T > 0`, `T_c > 0`
(then `v² + 2bv - b² > 2b² > 0`).
-/

namespace Blind.PRAcentric

open Real MeasureTheory intervalIntegral

/-- Published Peng–Robinson correlation. -/
def kappa (ω : ℝ) : ℝ := 0.37464 + 1.54226 * ω - 0.26992 * ω ^ 2

/-- Soave temperature function. -/
noncomputable def aT (ac κ Tc T : ℝ) : ℝ := ac * (1 + κ * (1 - Real.sqrt (T / Tc))) ^ 2

/-- Peng–Robinson pressure (meaningful for `v > b`, `T > 0`, `Tc > 0`). -/
noncomputable def prP (R b ac κ Tc : ℝ) (v T : ℝ) : ℝ :=
  R * T / (v - b) - aT ac κ Tc T / (v ^ 2 + 2 * b * v - b ^ 2)

/-- Critical point: `T_c > 0`, `v_c > b`, flat and inflected critical isotherm, `P_c` the pressure. -/
def IsCriticalPoint (R b ac κ : ℝ) (Tc vc Pc : ℝ) : Prop :=
  0 < Tc ∧ b < vc ∧
  deriv (fun v => prP R b ac κ Tc v Tc) vc = 0 ∧
  deriv (deriv (fun v => prP R b ac κ Tc v Tc)) vc = 0 ∧
  Pc = prP R b ac κ Tc vc Tc

/-- Maxwell equal-area coexistence at temperature `T`. -/
def IsCoexistence (R b ac κ Tc : ℝ) (T vl vg ps : ℝ) : Prop :=
  b < vl ∧ vl < vg ∧
  prP R b ac κ Tc vl T = ps ∧ prP R b ac κ Tc vg T = ps ∧
  (∫ v in vl..vg, prP R b ac κ Tc v T) = ps * (vg - vl)

/-- Pitzer acentric factor `-log₁₀(p_s/P_c) - 1` (used only with `p_s/P_c > 0`). -/
noncomputable def acentric (ps Pc : ℝ) : ℝ := -Real.logb 10 (ps / Pc) - 1

theorem coexistence_exists (R b ac : ℝ) (hR : 0 < R) (hb : 0 < b) (hac : 0 < ac)
    (Tc vc Pc : ℝ) (hc : IsCriticalPoint R b ac (kappa 1) Tc vc Pc) :
    ∃ vl vg ps, IsCoexistence R b ac (kappa 1) Tc (7 / 10 * Tc) vl vg ps := by
  sorry

theorem coexistence_numbers (R b ac : ℝ) (hR : 0 < R) (hb : 0 < b) (hac : 0 < ac)
    (Tc vc Pc : ℝ) (hc : IsCriticalPoint R b ac (kappa 1) Tc vc Pc)
    (vl vg ps : ℝ) (hco : IsCoexistence R b ac (kappa 1) Tc (7 / 10 * Tc) vl vg ps) :
    0 < ps / Pc ∧
    Checked.Records.RoundsTo (ps / Pc) (114 / 10000) 4 ∧
    Checked.Records.RoundsTo (acentric ps Pc) (942 / 1000) 3 ∧
    acentric ps Pc ≠ 1 := by
  sorry

/-- Full claim: coexistence exists, and every coexistence state has the stated numbers, so
the computed acentric factor is not the input `ω = 1`. -/
theorem pr_acentric (R b ac : ℝ) (hR : 0 < R) (hb : 0 < b) (hac : 0 < ac)
    (Tc vc Pc : ℝ) (hc : IsCriticalPoint R b ac (kappa 1) Tc vc Pc) :
    (∃ vl vg ps, IsCoexistence R b ac (kappa 1) Tc (7 / 10 * Tc) vl vg ps) ∧
    ∀ vl vg ps, IsCoexistence R b ac (kappa 1) Tc (7 / 10 * Tc) vl vg ps →
      0 < ps / Pc ∧
      Checked.Records.RoundsTo (ps / Pc) (114 / 10000) 4 ∧
      Checked.Records.RoundsTo (acentric ps Pc) (942 / 1000) 3 ∧
      acentric ps Pc ≠ 1 := by
  sorry

end Blind.PRAcentric
