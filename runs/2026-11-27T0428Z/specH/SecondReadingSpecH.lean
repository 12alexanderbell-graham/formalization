import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Basic

/-!
# Second reading H: specifications of four cosmological quantities / model conditions

Sources (verbatim LaTeX excerpts in `runs/2026-11-27T0428Z/sources/`):
* Bamba, Capozziello, Nojiri, Odintsov 2012 (arXiv:1205.3421v3), file `bamba2012_1205.3421v3.md`;
* Aviles, Gruber, Luongo, Quevedo 2012 (arXiv:1204.2007), file `aviles2012_1204.2007.md`;
* Capozziello, Lazkoz, Salzano 2011 (arXiv:1104.3096), file `capozziello2011_1104.3096.md`.

Line numbers below are those of the transcription files (`.md`); the transcription headers give
the corresponding lines of the LaTeX sources.

Conventions: `c = 1`; `a : ℝ → ℝ` is the scale factor in cosmic time, not normalised; the Hubble
rate is `H(t) = a'(t) / a(t)` (Aviles line 72, `H ≡ (1/a) da/dt`); the cosmological redshift of
light emitted at `t` and received at `t₀` is `z = a(t₀)/a(t) - 1`, i.e. `1 + z = a(t₀)/a(t)`
(Bamba line 25, `z ≡ a₀/a - 1`, there with `a₀ = 1`; here `a₀ = a(t₀)` is kept explicit).
-/

namespace Checked.Trust.SecondReadingSpecH

/-- **Curvature parameter of Bamba et al. 2012, §X.**
`k K a t₀` is the present spatial-curvature density parameter `Ω_K^{(0)}` of §X.  In §X the
distance coefficients contain the combination `K c² / (H₀² a₀²)` (Bamba lines 41, 45, 52; e.g.
`𝒟_A² = (1/6)[11 + 7q₀ + 3q₀² − j₀ − K c²/(H₀² a₀²)]`), and lines 58–61 define
`Ω₀ = 1 + K c²/(H₀² a₀²)` and equivalently `Ω₀ = 1 − Ω_K^{(0)}`.  Hence, in that section's sign
convention, `Ω_K^{(0)} = − K / (a₀² H₀²)` (with `c = 1`), with `a₀ = a(t₀)` and
`H₀ = a'(t₀)/a(t₀)` the Hubble rate at `t₀`.

Convention chosen: the brief asks for "the dimensionless spatial curvature parameter"; the only
named curvature parameter in §X is `Ω_K^{(0)}` (line 61), so the value is `−K/(a₀² H₀²)`, i.e. the
term that enters `𝒟_A²` with a `+` sign.  (The bare ratio `K/(a₀²H₀²) = Ω₀ − 1` would be the
opposite sign; see the report.)  Note that Aviles et al. (line 36) use the opposite sign,
`Ω_k ≡ Ω₀ − 1`; that is not followed here.

Determined arguments: every `K`, and every `a`, `t₀` with `a(t₀) > 0` and `a` differentiable at
`t₀` with `a'(t₀) ≠ 0` (so that `H₀` exists and is non-zero, which the division by `H₀²`
needs).  Nothing is stated where `H₀` is zero or undefined or `a(t₀) ≤ 0`. -/
structure CurvParamSpecH (k : ℝ → (ℝ → ℝ) → ℝ → ℝ) : Prop where
  /-- The defining formula `Ω_K^{(0)} = 1 − Ω₀ = − K c² / (H₀² a₀²)` (Bamba lines 58–61, with the
  combination as it appears in lines 41, 45, 52), `c = 1`, `a₀ = a(t₀)`,
  `H₀ = a'(t₀)/a(t₀)`.  Side conditions `a(t₀) > 0` (a physical scale factor; my choice) and
  `a'(t₀) ≠ 0` (so `H₀ ≠ 0`; this also forces `a` differentiable at `t₀`). -/
  formula : ∀ (K : ℝ) (a : ℝ → ℝ) (t₀ : ℝ), 0 < a t₀ → deriv a t₀ ≠ 0 →
    k K a t₀ = - K / (a t₀ ^ 2 * (deriv a t₀ / a t₀) ^ 2)

/-- **Ricci scalar of the flat FLRW metric as used in Bamba et al. 2012, §XI.**
`R a t` is the scalar curvature in the form of the printed equation (11.6) (label `eq: rvsh`,
Bamba lines 159–165): `R = − 6 (Ḣ + 2 H²)`, with `H = ȧ/a` the Hubble rate.

Convention: the source is inconsistent between sections.  §VIII.C (Bamba lines 32 and 35) writes
`R = 6 (Ḣ + 2H²)`, whereas §XI (line 163) writes `R = −6 (Ḣ + 2H²)`.  As the brief instructs,
the §XI sign (overall minus) is followed.  Equivalently, since `Ḣ = ä/a − H²`,
`R = −6 (ä/a + (ȧ/a)²)`.

Determined arguments: every `a`, `t` with `a(t) > 0`, `a` differentiable on a neighbourhood of
`t` and `ȧ` differentiable at `t` (so that `H` is defined near `t` and `Ḣ(t)` exists).  Nothing
is stated elsewhere. -/
structure RicciFlatSpecH (R : (ℝ → ℝ) → ℝ → ℝ) : Prop where
  /-- Bamba eq. (11.6), line 163: `R = −6 (Ḣ + 2H²)` with `H(s) = a'(s)/a(s)` and `Ḣ` its time
  derivative at `t`.  Side conditions (my choice, where `Ḣ` is meaningful): `a(t) > 0`, `a`
  differentiable at every point near `t`, and `a'` differentiable at `t`. -/
  formula : ∀ (a : ℝ → ℝ) (t : ℝ), 0 < a t → (∀ᶠ s in nhds t, DifferentiableAt ℝ a s) →
    DifferentiableAt ℝ (deriv a) t →
    R a t = -6 * (deriv (fun s => deriv a s / a s) t + 2 * (deriv a t / a t) ^ 2)

/-- **Flat ΛCDM model as stated by Aviles, Gruber, Luongo, Quevedo 2012.**
`P Ω a t₀` holds iff the expansion rate obeys (Aviles line 113)
`H = H₀ √(Ω_m (1+z)³ + 1 − Ω_m)` with `Ω_m = Ω`, where `H(t) = a'(t)/a(t)`, `H₀ = H(t₀)` and
`1 + z = a(t₀)/a(t)`.  Flatness (`k = 0`, lines 39–40), no radiation (footnote, lines 11–12 and
line 105 "neglecting radiation components at late times") and `Ω_Λ = 1 − Ω_m` are all built into
that formula.

Where it holds: on a neighbourhood of `t₀` (both sides).  Words that decided it: the model is
"for our purposes and the redshifts involved sufficiently described" (lines 108–109), radiation is
neglected only "at late times" (line 11, line 105), and the formula is used only to compute the
cosmographic series, i.e. derivatives of `a` at `t₀` (lines 112–113, 17–20), which need the
relation on a two-sided neighbourhood of `t₀`.  A global ("all times") reading is not taken,
because a real ΛCDM scale factor reaches `a = 0` at a finite past time, where `z` is undefined.
The relation is written as the equivalent ODE `a' = a · H₀ √(Ω (a₀/a)³ + 1 − Ω)` near `t₀`
(equivalent, near `t₀` where `a > 0`, to "`a` differentiable and `a'/a = H₀ √(…)`").

Side conditions (outside the equivalence; where the source's notion is meaningful): `a(t₀) > 0`
and `a'(t₀) ≠ 0` (so `H₀ ≠ 0`, which a density parameter `Ω_m = ρ_m/(3H₀²)` needs).  The source
is silent on the sign of `H₀`; my choice is not to require `H₀ > 0` (the formula `H = H₀ √…`
covers either sign).  `Ω` is unrestricted (near `z = 0` the radicand is close to `1`).
Determined: the truth of `P Ω a t₀` for every `Ω` and every `a`, `t₀` with these side
conditions. -/
structure FlatLCDMSpecH (P : ℝ → (ℝ → ℝ) → ℝ → Prop) : Prop where
  /-- Aviles line 113: `H = H₀ √(Ω_m (1+z)³ + 1 − Ω_m)`, read on a neighbourhood of `t₀`, with
  `H = a'/a`, `H₀ = a'(t₀)/a(t₀)` and `1 + z = a(t₀)/a(t)`, written as
  `a'(t) = a(t) · H₀ · √(Ω (a(t₀)/a(t))³ + 1 − Ω)`. -/
  iff : ∀ (Ω : ℝ) (a : ℝ → ℝ) (t₀ : ℝ), 0 < a t₀ → deriv a t₀ ≠ 0 →
    (P Ω a t₀ ↔
      ∀ᶠ t in nhds t₀,
        HasDerivAt a
          (a t * ((deriv a t₀ / a t₀) * Real.sqrt (Ω * (a t₀ / a t) ^ (3 : ℕ) + 1 - Ω))) t)

/-- **Flat CDM + CPL dark energy as stated by Capozziello, Lazkoz, Salzano 2011.**
`P Ω w₀ wₐ a t₀` holds iff (Capozziello lines 15–21) the dimensionless Hubble rate
`E = H/H₀` satisfies
`E²(z) = Ω_m (1+z)³ + Ω_X (1+z)^{3(1+w₀+wₐ)} exp(−3 wₐ z/(1+z))` with `Ω_X = 1 − Ω_m`
("because of the flatness assumption", line 21), `Ω_m = Ω`, `H = a'/a`, `H₀ = H(t₀)`,
`1 + z = a(t₀)/a(t)`.  The CPL equation of state `w = w₀ + wₐ(1 − a) = w₀ + wₐ z/(1+z)`
(line 12) is written there with `a₀ = 1`; with `a` unnormalised it is `w₀ + wₐ (1 − a/a₀)`,
consistent with the redshift form, which is what is used.

Since `E = H/H₀` and `E(0) = 1`, `E` is the positive square root near `z = 0`, so
`H = H₀ √(E²)`; this is written as the ODE `a' = a · H₀ · √(E²(z))` near `t₀`.

Where it holds: on a neighbourhood of `t₀` (both sides).  Words that decided it: the model is
used only "to determine the cosmographic parameters" (lines 22–25), via `d/dt = −(1+z)H d/dz`
applied at the present, i.e. derivatives at `t₀`; the source does not state a time range, and a
global reading would fail at the past singularity `a → 0`.  The power `(1+z)^{3(1+w₀+wₐ)}` is the
real power of the positive number `a(t₀)/a(t)`.

Side conditions (outside the equivalence): `a(t₀) > 0` and `a'(t₀) ≠ 0` (so `H₀ ≠ 0`; sign of
`H₀` not restricted, the source being silent).  `Ω`, `w₀`, `wₐ` unrestricted.  Determined: the
truth of `P Ω w₀ wₐ a t₀` for all `Ω, w₀, wₐ` and all `a, t₀` with these side conditions. -/
structure FlatCPLSpecH (P : ℝ → ℝ → ℝ → (ℝ → ℝ) → ℝ → Prop) : Prop where
  /-- Capozziello eq. `eq: ecpl` (lines 17–21) with `Ω_X = 1 − Ω_m`, read on a neighbourhood of
  `t₀`: `a'(t) = a(t) · H₀ · √(Ω (1+z)³ + (1−Ω)(1+z)^{3(1+w₀+wₐ)} e^{−3wₐ z/(1+z)})` with
  `1 + z = a(t₀)/a(t)`, `z = a(t₀)/a(t) − 1`, `H₀ = a'(t₀)/a(t₀)`. -/
  iff : ∀ (Ω w₀ wₐ : ℝ) (a : ℝ → ℝ) (t₀ : ℝ), 0 < a t₀ → deriv a t₀ ≠ 0 →
    (P Ω w₀ wₐ a t₀ ↔
      ∀ᶠ t in nhds t₀,
        HasDerivAt a
          (a t * ((deriv a t₀ / a t₀) *
            Real.sqrt (Ω * (a t₀ / a t) ^ (3 : ℕ)
              + (1 - Ω) * (a t₀ / a t) ^ (3 * (1 + w₀ + wₐ))
                * Real.exp (-(3 * wₐ * (a t₀ / a t - 1)) / (a t₀ / a t))))) t)

end Checked.Trust.SecondReadingSpecH
