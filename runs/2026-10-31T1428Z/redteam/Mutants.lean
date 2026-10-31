import Mathlib

/-!
Red-team mutants of
  IsMaxwellCoexistence p vl vg ps :=
    vl < vg ∧ p vl = ps ∧ p vg = ps ∧ ∫ v in vl..vg, p v = ps * (vg - vl)

Notation used in the counterexamples: "S" is the symmetric (antisymmetric-about-the-midpoint)
cubic isotherm  S(v) = 1 + w^3 - w,  w = v - 1.  On S, (vl, vg, ps) = (0, 2, 1) is a genuine
Maxwell state: S 0 = S 2 = 1 and ∫_0^2 S = 2 = 1 * 2.
-/

namespace RedTeam.Maxwell

/-- 01. Non-strict ordering `vl ≤ vg`.
Disagrees: p = fun _ => 1, (vl, vg, ps) = (0, 0, 1).  All four conjuncts hold (integral over an
empty interval is 0 = 1 * 0) but the correct definition fails at `0 < 0`.  Physically the
"coexisting phases" are one and the same state: there is no liquid/gas distinction, the
construction is vacuous (any point of any isotherm is a "coexistence"). -/
def mutant01 (p : ℝ → ℝ) (vl vg ps : ℝ) : Prop :=
  vl ≤ vg ∧ p vl = ps ∧ p vg = ps ∧ ∫ v in vl..vg, p v = ps * (vg - vl)

/-- 02. Mean-value / midpoint-rule formulation: the "average pressure" is replaced by the
pressure at the mid-volume, i.e. `p ((vl+vg)/2) = ps`.  Equal to the correct definition on
every isotherm that is antisymmetric about the midpoint (all symmetric test cubics).
Disagrees: p v = v(v-1)(v-2)(v-3), (vl, vg, ps) = (0, 2, 0): p 0 = p 1 = p 2 = 0 so the mutant
holds, but with w = v-1, ∫_0^2 p = ∫_{-1}^1 (w^4 - 2w^3 - w^2 + 2w) dw = 2/5 - 2/3 = -4/15 ≠ 0.
Physically the tie line does not balance the two lobes; the area rule is not a point condition. -/
def mutant02 (p : ℝ → ℝ) (vl vg ps : ℝ) : Prop :=
  vl < vg ∧ p vl = ps ∧ p vg = ps ∧ p ((vl + vg) / 2) = ps

/-- 03. Gibbs energy with the wrong sign of the `p v` term: g = f - p v (f = -∫ p dv, so the
equality f(vg) - ps vg = f(vl) - ps vl) i.e. `∫ p = -ps (vg - vl)`.  Agrees with the correct
definition whenever ps = 0 (any isotherm test with zero saturation pressure) and in every
pressure-shifted-by-zero test.
Disagrees: S, (0, 2, 1): correct holds (∫ = 2 = 1*2); mutant needs 2 = -2.  Physically, the
chemical potential is μ = f + p v (g = u - Ts + pv); with the minus sign equal "μ" is not
equal Gibbs energy and gives negative-pressure-shifted areas. -/
def mutant03 (p : ℝ → ℝ) (vl vg ps : ℝ) : Prop :=
  vl < vg ∧ p vl = ps ∧ p vg = ps ∧
    (-(∫ v in vl..vg, p v)) - ps * vg = 0 - ps * vl

/-- 04. Equality of Helmholtz free energies only: f(vg) = f(vl) with f' = -p, i.e. `∫ p = 0`.
Agrees with the correct definition when ps = 0.
Disagrees: S, (0, 2, 1): ∫_0^2 S = 2 ≠ 0.  Physically, phases in equilibrium at fixed (T, p)
must have equal Gibbs (not Helmholtz) energy; Helmholtz equality misses the p Δv work term. -/
def mutant04 (p : ℝ → ℝ) (vl vg ps : ℝ) : Prop :=
  vl < vg ∧ p vl = ps ∧ p vg = ps ∧ (-(∫ v in vl..vg, p v)) = 0

/-- 05. Equal *unsigned* half-areas about the mid-volume:
∫_{vl}^{m} |p - ps| = ∫_{m}^{vg} |p - ps|, m = (vl+vg)/2.  On odd-about-midpoint cubics the two
lobes have equal absolute area, as required; also true for every odd-symmetric test.
Disagrees: p v = v (v - 2), (vl, vg, ps) = (0, 2, 0): the parabola is symmetric about 1 so the
unsigned halves are equal, yet ∫_0^2 p = 8/3 - 4 = -4/3 ≠ 0 (both "lobes" lie on the same side
of the tie line: this is the liquid / unstable-root type pair, not a coexistence).  Also
fails to detect asymmetric lobes whose absolute areas happen to split evenly at the midpoint. -/
def mutant05 (p : ℝ → ℝ) (vl vg ps : ℝ) : Prop :=
  vl < vg ∧ p vl = ps ∧ p vg = ps ∧
    ∫ v in vl..((vl + vg) / 2), |p v - ps| = ∫ v in ((vl + vg) / 2)..vg, |p v - ps|

/-- 06. The area is balanced against `p vl` only: the equal-pressure condition at the gas end
is forgotten (`p vg = ps` missing), the area condition being written as ∫ (p - ps) = 0.
Indistinguishable from the correct definition on every genuine coexistence, so any test that
only supplies true states passes.
Disagrees: p v = 2v - 3v^2, (vl, vg, ps) = (0, 1, 0): p 0 = 0, ∫_0^1 p = 1 - 1 = 0, but
p 1 = -1 ≠ 0.  Physically the "gas" is at a different pressure than the liquid: no mechanical
equilibrium between the phases. -/
def mutant06 (p : ℝ → ℝ) (vl vg ps : ℝ) : Prop :=
  vl < vg ∧ p vl = ps ∧ ∫ v in vl..vg, (p v - ps) = 0

/-- 07. Equal-area rule applied in the wrong variable: integrating over molar density
ρ = 1/v instead of volume, ∫_{1/vg}^{1/vl} p(1/ρ) dρ = ps (1/vl - 1/vg).  Looks like a
harmless change of variables (and is true for p constant and, trivially, for ps-flat curves).
Disagrees: p v = 1 + w^3 - w with w = v - 2, (vl, vg, ps) = (1, 3, 1): correct holds
(p 1 = p 3 = 1, ∫ = 2).  Mutant: ∫_1^3 (w^3 - w)/v^2 dv = ∫_{-1}^{1} (x^3 - x)/(x+2)^2 dx
= ∫_0^1 (x^3-x)(1/(x+2)^2 - 1/(2-x)^2) dx > 0 (both factors negative), so it fails.
Physically dv = -dρ/ρ², the work integral ∫ p dv is not ∫ p dρ (Jacobian dropped). -/
def mutant07 (p : ℝ → ℝ) (vl vg ps : ℝ) : Prop :=
  0 < vl ∧ vl < vg ∧ p vl = ps ∧ p vg = ps ∧
    ∫ ρ in (1 / vg)..(1 / vl), p (1 / ρ) = ps * (1 / vl - 1 / vg)

/-- 08. One-sided area condition `∫ p ≥ ps (vg - vl)` (net area on the "gas side" is not
negative) instead of equality.  Holds on all true coexistence states, so true-state tests
pass, and the endpoints of a symmetric loop are accepted.
Disagrees: p v = 2v - v^2, (vl, vg, ps) = (0, 2, 0): p 0 = p 2 = 0, ∫_0^2 p = 4/3 ≥ 0 so the
mutant holds, but 4/3 ≠ 0.  Physically the pressure ps is then not the equilibrium pressure
(chemical potentials differ; a strictly lower or higher ps would be needed); it admits a
whole interval of pressures per isotherm instead of the single Maxwell pressure. -/
def mutant08 (p : ℝ → ℝ) (vl vg ps : ℝ) : Prop :=
  vl < vg ∧ p vl = ps ∧ p vg = ps ∧ ps * (vg - vl) ≤ ∫ v in vl..vg, p v

/-- 09. Swapped phase labelling: the liquid volume is declared to be the larger one,
`vg < vl`, with the integral still written from `vl` to `vg` (so it is oriented backwards and
the right-hand side `ps (vg - vl)` has a consistent sign).  Every equation reads like the
Maxwell rule, and the pair (2, 0) on S satisfies it with ∫_2^0 S = -2 = 1 * (0 - 2).
Disagrees: S with (vl, vg, ps) = (0, 2, 1): correct holds, mutant fails at `2 < 0`; conversely
(2, 0, 1) is accepted by the mutant, rejected by the correct definition.  Physically the liquid
is the denser phase (smaller molar volume): this assigns the labels the wrong way round. -/
def mutant09 (p : ℝ → ℝ) (vl vg ps : ℝ) : Prop :=
  vg < vl ∧ p vl = ps ∧ p vg = ps ∧ ∫ v in vl..vg, p v = ps * (vg - vl)

/-- 10. Equal *unsigned* lobes about an interior point `vm` of the tie line (a point where the
isotherm crosses `ps`).  For a cubic loop the sign alternates at `vm`, so unsigned equality is
the same as cancellation of the signed areas, and the mutant is equivalent to the correct one on
every ordinary van der Waals isotherm.
Disagrees: p v = v (v - 2) (v - 1)^2, (vl, vg, ps) = (0, 2, 0) with vm = 1 (a touching /
double root, no sign change): the lobes are mirror images so unsigned areas agree, but with
w = v - 1, ∫_0^2 p = ∫_{-1}^{1} (w^4 - w^2) dw = 2/5 - 2/3 = -4/15 ≠ 0.  This is the
"liquid / unstable root" pair: the tie line touches the curve instead of enclosing two opposite
lobes, there is no phase equilibrium. -/
def mutant10 (p : ℝ → ℝ) (vl vg ps : ℝ) : Prop :=
  vl < vg ∧ p vl = ps ∧ p vg = ps ∧
    ∃ vm, vl < vm ∧ vm < vg ∧ p vm = ps ∧
      ∫ v in vl..vm, |p v - ps| = ∫ v in vm..vg, |p v - ps|

end RedTeam.Maxwell
