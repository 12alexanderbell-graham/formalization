import Mathlib
import Checked.Records.Basic

open MeasureTheory intervalIntegral

namespace Blind.SRKAcentric

/-- Soave's 1972 correlation κ(ω) = 0.480 + 1.574 ω − 0.176 ω². -/
noncomputable def kappa (ω : ℝ) : ℝ := 0.480 + 1.574 * ω - 0.176 * ω ^ 2

/-- Soave's a(T) = a_c (1 + κ (1 − √(T/T_c)))², with κ = κ(1) (ω = 1). -/
noncomputable def aT (ac Tc T : ℝ) : ℝ :=
  ac * (1 + kappa 1 * (1 - Real.sqrt (T / Tc))) ^ 2

/-- SRK pressure P(v,T) = R T/(v−b) − a(T)/(v(v+b)). -/
noncomputable def P (R ac Tc b v T : ℝ) : ℝ :=
  R * T / (v - b) - aT ac Tc T / (v * (v + b))

/-- (Tc, vc) is a critical point: vc > b and the critical isotherm has vanishing first and
second volume derivatives at vc. -/
def IsCritical (R ac b Tc vc : ℝ) : Prop :=
  b < vc ∧ deriv (fun v => P R ac Tc b v Tc) vc = 0 ∧
    deriv (deriv (fun v => P R ac Tc b v Tc)) vc = 0

/-- Maxwell equal-area coexistence state on the isotherm T. -/
def IsMaxwell (R ac Tc b T ps vl vg : ℝ) : Prop :=
  b < vl ∧ vl < vg ∧ P R ac Tc b vl T = ps ∧ P R ac Tc b vg T = ps ∧
    ∫ v in vl..vg, P R ac Tc b v T = ps * (vg - vl)

theorem srk_acentric (R ac b Tc vc : ℝ) (hR : 0 < R) (hac : 0 < ac) (hb : 0 < b)
    (hTc : 0 < Tc) (hcrit : IsCritical R ac b Tc vc)
    (ps vl vg : ℝ) (hM : IsMaxwell R ac Tc b (0.7 * Tc) ps vl vg) :
    Checked.Records.RoundsTo (ps / P R ac Tc b vc Tc) 0.0102 4 ∧
    Checked.Records.RoundsTo (-Real.logb 10 (ps / P R ac Tc b vc Tc) - 1) 0.992 3 := by
  sorry

theorem srk_exists (R ac b Tc vc : ℝ) (hR : 0 < R) (hac : 0 < ac) (hb : 0 < b)
    (hTc : 0 < Tc) (hcrit : IsCritical R ac b Tc vc) :
    ∃ ps vl vg, IsMaxwell R ac Tc b (0.7 * Tc) ps vl vg := by
  sorry

end Blind.SRKAcentric
