import Checked.Chemistry.CubicEOS
import Checked.Chemistry.Coexistence
import Checked.Trust.SpecAgreementEF

/-!
# The junk-value admissions of `IsCriticalIsotherm` and `IsMaxwellCoexistence` are immaterial for every
cubic-equation-of-state state the headlines talk about (run 2026-11-27T1028Z, part 3 (d) of
`runs/2026-11-27T0228Z/README.md`)

Readers E and F (run 2026-11-27T0228Z) disagree with the program's two conditions only through Lean's junk
values: `deriv` is zero where no derivative exists, `∫` is zero for a non-integrable function
(`not_meets_IsCriticalIsotherm_E/F`, `not_meets_IsMaxwellCoexistence_E/F`); their specifications determine
the program's condition wherever the derivatives exist / the isotherm is integrable
(`pins_IsCriticalIsotherm_E/F`, `pins_IsMaxwellCoexistence_E/F`). Question (d): should the definitions be
changed (a relock and every chemistry headline re-proved)?

Answer, proved here: no change is needed for any headline. Every chemistry headline that uses either condition
does so for a generalized cubic isotherm `cubicP R a b u w T` at volumes above the co-volume (`b < v`, `b < vl`),
with `u > −2`, `1 + u + w > 0` (van der Waals, Redlich–Kwong, Soave, Peng–Robinson 1976 and 1978). There:
* the isotherm and its derivative are differentiable at every volume above `b` (`cubicP_diff`,
  `cubicP_deriv_diff`), so the program's critical-point condition is equivalent to readers E's and F's
  (`critical_agrees_E`, `critical_agrees_F`);
* the isotherm is continuous, hence integrable, on every interval of volumes above `b`
  (`cubicP_intervalIntegrable`), so the program's equal-area condition is equivalent to readers E's and F's
  for every state with liquid volume above `b` (`coexistence_agrees_E`, `coexistence_agrees_F`).
The junk witnesses of the disagreements (a pressure with a jump; the reciprocal of `v` minus `v`, across its pole) are not cubic
isotherms above the co-volume. The conditions stay as they are; what the claims page should add is that the
disagreement does not reach these states.
-/

namespace Checked.Trust.JunkImmaterial

open Filter Topology MeasureTheory Checked.Chemistry.CubicEOS Checked.Chemistry.Coexistence
  Checked.Trust.SpecAgreement

/-- The denominator `v² + u b v + w b²` is positive at every volume `v ≥ b` when `b > 0`, `u > −2`,
`1 + u + w > 0` (the argument of `exists_unique_critical`). -/
lemma denom_pos (b u w v : ℝ) (hb : 0 < b) (hu : -2 < u) (h1 : 0 < 1 + u + w) (hv : b ≤ v) :
    0 < v ^ 2 + u * b * v + w * b ^ 2 := by
  have e : v ^ 2 + u * b * v + w * b ^ 2 = b ^ 2 * (1 + u + w) + (v - b) * (v + b + u * b) := by ring
  rw [e]
  have : 0 ≤ (v - b) * (v + b + u * b) := mul_nonneg (by linarith) (by nlinarith)
  have : 0 < b ^ 2 * (1 + u + w) := by positivity
  linarith

lemma cubicP_diff (R a b u w T v : ℝ) (hv : b < v) (hD : v ^ 2 + u * b * v + w * b ^ 2 ≠ 0) :
    DifferentiableAt ℝ (cubicP R a b u w T) v :=
  (hasDerivAt_P R a b u w T v (by linarith) hD).differentiableAt

lemma cubicP_deriv_diff (R a b u w T v : ℝ) (hv : b < v) (hD : v ^ 2 + u * b * v + w * b ^ 2 ≠ 0) :
    DifferentiableAt ℝ (deriv (cubicP R a b u w T)) v := by
  have hvb : v - b ≠ 0 := by linarith
  have hev : deriv (cubicP R a b u w T) =ᶠ[𝓝 v]
      (fun x => -(R * T) / (x - b) ^ 2 + a * (2 * x + u * b) / (x ^ 2 + u * b * x + w * b ^ 2) ^ 2) := by
    have hc : ContinuousAt (fun x => (x - b, x ^ 2 + u * b * x + w * b ^ 2)) v := by fun_prop
    have hopen : {q : ℝ × ℝ | q.1 ≠ 0 ∧ q.2 ≠ 0} ∈ 𝓝 (v - b, v ^ 2 + u * b * v + w * b ^ 2) :=
      (isOpen_ne_fun continuous_fst continuous_const |>.inter
        (isOpen_ne_fun continuous_snd continuous_const)).mem_nhds ⟨hvb, hD⟩
    filter_upwards [hc hopen] with x hx
    exact (hasDerivAt_P R a b u w T x hx.1 hx.2).deriv
  exact (hasDerivAt_P1 R a b u w T v hvb hD).differentiableAt.congr_of_eventuallyEq hev

lemma cubicP_intervalIntegrable (R a b u w T vl vg : ℝ) (hb : 0 < b) (hu : -2 < u) (h1 : 0 < 1 + u + w)
    (hl : b < vl) (hg : b < vg) :
    IntervalIntegrable (cubicP R a b u w T) volume vl vg := by
  apply ContinuousOn.intervalIntegrable
  intro x hx
  have hx' : b < x := by
    rcases Set.mem_uIcc.1 hx with h | h <;> linarith [h.1]
  have hD := denom_pos b u w x hb hu h1 hx'.le
  exact (cubicP_diff R a b u w T x hx' hD.ne').continuousAt.continuousWithinAt

/-- Reader E's critical-point specification and the program's condition agree at every cubic isotherm
volume above the co-volume. -/
theorem critical_agrees_E (P : (ℝ → ℝ) → ℝ → Prop) (h : SecondReadingSpecE.CriticalSpecE P)
    (R a b u w T v : ℝ) (hb : 0 < b) (hu : -2 < u) (h1 : 0 < 1 + u + w) (hv : b < v) :
    P (cubicP R a b u w T) v ↔ IsCriticalIsotherm (cubicP R a b u w T) v :=
  have hD := (denom_pos b u w v hb hu h1 hv.le).ne'
  pins_IsCriticalIsotherm_E P h _ v (cubicP_diff R a b u w T v hv hD) (cubicP_deriv_diff R a b u w T v hv hD)

theorem critical_agrees_F (P : (ℝ → ℝ) → ℝ → Prop) (h : SecondReadingSpecF.CriticalSpecF P)
    (R a b u w T v : ℝ) (hb : 0 < b) (hu : -2 < u) (h1 : 0 < 1 + u + w) (hv : b < v) :
    P (cubicP R a b u w T) v ↔ IsCriticalIsotherm (cubicP R a b u w T) v :=
  have hD := (denom_pos b u w v hb hu h1 hv.le).ne'
  pins_IsCriticalIsotherm_F P h _ v (cubicP_diff R a b u w T v hv hD) (cubicP_deriv_diff R a b u w T v hv hD)

/-- Reader E's coexistence specification and the program's condition agree for every cubic isotherm state
with both volumes above the co-volume. -/
theorem coexistence_agrees_E (P : (ℝ → ℝ) → ℝ → ℝ → ℝ → Prop) (h : SecondReadingSpecE.CoexistenceSpecE P)
    (R a b u w T vl vg ps : ℝ) (hb : 0 < b) (hu : -2 < u) (h1 : 0 < 1 + u + w) (hl : b < vl)
    (hg : b < vg) :
    P (cubicP R a b u w T) vl vg ps ↔ IsMaxwellCoexistence (cubicP R a b u w T) vl vg ps :=
  pins_IsMaxwellCoexistence_E P h _ vl vg ps (cubicP_intervalIntegrable R a b u w T vl vg hb hu h1 hl hg)

theorem coexistence_agrees_F (P : (ℝ → ℝ) → ℝ → ℝ → ℝ → Prop) (h : SecondReadingSpecF.CoexistenceSpecF P)
    (R a b u w T vl vg ps : ℝ) (hb : 0 < b) (hu : -2 < u) (h1 : 0 < 1 + u + w) (hl : b < vl)
    (hg : b < vg) :
    P (cubicP R a b u w T) vl vg ps ↔ IsMaxwellCoexistence (cubicP R a b u w T) vl vg ps :=
  pins_IsMaxwellCoexistence_F P h _ vl vg ps (cubicP_intervalIntegrable R a b u w T vl vg hb hu h1 hl hg)

/-- On the program's side the gas volume of a coexistence state with liquid volume above `b` is itself above
`b` (`vl < vg` is part of the condition), so `coexistence_agrees_E/F` cover every state a headline with
`b < vl` quantifies over. -/
theorem coexistence_agrees_of_liquid_E (P : (ℝ → ℝ) → ℝ → ℝ → ℝ → Prop)
    (h : SecondReadingSpecE.CoexistenceSpecE P)
    (R a b u w T vl vg ps : ℝ) (hb : 0 < b) (hu : -2 < u) (h1 : 0 < 1 + u + w) (hl : b < vl)
    (hc : IsMaxwellCoexistence (cubicP R a b u w T) vl vg ps) :
    P (cubicP R a b u w T) vl vg ps :=
  (coexistence_agrees_E P h R a b u w T vl vg ps hb hu h1 hl (hl.trans hc.1)).2 hc

theorem coexistence_agrees_of_liquid_F (P : (ℝ → ℝ) → ℝ → ℝ → ℝ → Prop)
    (h : SecondReadingSpecF.CoexistenceSpecF P)
    (R a b u w T vl vg ps : ℝ) (hb : 0 < b) (hu : -2 < u) (h1 : 0 < 1 + u + w) (hl : b < vl)
    (hc : IsMaxwellCoexistence (cubicP R a b u w T) vl vg ps) :
    P (cubicP R a b u w T) vl vg ps :=
  (coexistence_agrees_F P h R a b u w T vl vg ps hb hu h1 hl (hl.trans hc.1)).2 hc

end Checked.Trust.JunkImmaterial
