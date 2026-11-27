import Checked.Cosmography.FRCosmo
import Checked.Cosmography.BambaZ
import Checked.Cosmography.CPLCoefficients
import Checked.Cosmography.LCDMCoefficients
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Basic

namespace Checked.Trust.SecondReadingSpecG

/-- Hubble rate `H = a'/a` of a scale factor (aviles2012 line 72: `H ≡ (1/a) da/dt`). -/
noncomputable def hubble (a : ℝ → ℝ) (t : ℝ) : ℝ := deriv a t / a t

/-- Item 1. The curvature parameter of the cosmographic distance expansions of Bamba et al. 2012 §X.

Source (bamba2012 lines 9825-9851): the coefficients of the angular-diameter distance series contain
`- K c² / (H₀² a₀²)` (with `c = 1`), and line 59 defines `Ω₀ = 1 + K c²/(H₀² a₀²)`. So the
dimensionless curvature parameter is `K / (H₀² a₀²)` = `Ω₀ - 1`, with the sign exactly as in the printed
formulas (positive for `K > 0`), `H₀ = a'(t₀)/a(t₀)` the Hubble rate at `t₀`.
Determined: all `K, a, t₀` with `a t₀ ≠ 0` and `H(t₀) ≠ 0` (equivalently `a t₀ ≠ 0`, `deriv a t₀ ≠ 0`).
Undetermined (source notion undefined): `a t₀ = 0` or `H₀ = 0`.
The source normalises `a₀ = 1` (bamba line 25) but the brief does not, so `a(t₀)` is kept. -/
structure CurvParamSpecG (k : ℝ → (ℝ → ℝ) → ℝ → ℝ) : Prop where
  /-- `k K a t₀ = K / (H₀² a(t₀)²)` with `H₀ = deriv a t₀ / a t₀` (bamba lines 59, 9825-9851). -/
  formula : ∀ (K : ℝ) (a : ℝ → ℝ) (t₀ : ℝ), a t₀ ≠ 0 → deriv a t₀ ≠ 0 →
    k K a t₀ = K / ((deriv a t₀ / a t₀) ^ 2 * (a t₀) ^ 2)

/-- Item 2. Ricci scalar of the flat FLRW metric as used in Bamba et al. 2012 §XI.

Source: printed equation (11.6), bamba line 163, `R = -6 (Ḣ + 2H²)`. NOTE the source is inconsistent:
§VIII.C (lines 7317 and 7515) uses `R = 6 (Ḣ + 2H²)`. As instructed, §XI's sign is followed (it
corresponds to the opposite curvature sign convention). Here `H = a'/a`, `Ḣ = dH/dt`.
Determined: all `a, t` with `a t ≠ 0`, `a` differentiable near `t` and `a'` differentiable at `t`
(so that `H` is differentiable at `t`). Elsewhere unconstrained. -/
structure RicciFlatSpecG (R : (ℝ → ℝ) → ℝ → ℝ) : Prop where
  /-- `R a t = -6 (Ḣ + 2 H²)` (bamba line 163; also stated in the abstract form via `H`). -/
  formula : ∀ (a : ℝ → ℝ) (t : ℝ), a t ≠ 0 →
    (∀ᶠ s in nhds t, DifferentiableAt ℝ a s) → DifferentiableAt ℝ (deriv a) t →
    R a t = -6 * (deriv (hubble a) t + 2 * (hubble a t) ^ 2)

/-- Item 3. Flat ΛCDM (dust + cosmological constant) in the sense of Aviles et al. 2012.

Source (aviles lines 112-113): `H = H₀ √(Ω_m (1+z)³ + 1 - Ω_m)`, redshift `1 + z = a(t₀)/a(t)`
(bamba line 25 definition, `z = a₀/a - 1`), `H = a'/a` (aviles line 72). The source gives `H` as a
function of `z` only, so I read it as a statement about the expansion history near the present.
Choices (source silent): the positive square root is taken, so `H₀ > 0` and `H > 0` (expanding
universe, as in the series of aviles line 62 with `H₀ > 0`); `a > 0`; the condition is imposed on a
neighbourhood of `t₀` (`∀ᶠ`), not at all times, since a FLRW solution need not exist for all times.
Determined: truth of `P Ω a t₀` for every `Ω, a, t₀`. For a given `Ω`, `H₀`, `a(t₀)` this fixes `a`
near `t₀`. `H₀` is free (the source's `E(z)` depends on `Ω` only). No restriction on `Ω` is imposed. -/
structure FlatLCDMSpecG (P : ℝ → (ℝ → ℝ) → ℝ → Prop) : Prop where
  /-- Equivalence with the expansion-rate law `H(t) = H(t₀) √(Ω (a(t₀)/a(t))³ + 1 - Ω)` near `t₀`. -/
  iff : ∀ (Ω : ℝ) (a : ℝ → ℝ) (t₀ : ℝ),
    P Ω a t₀ ↔
      (0 < a t₀ ∧ 0 < hubble a t₀ ∧
        ∀ᶠ s in nhds t₀, 0 < a s ∧ DifferentiableAt ℝ a s ∧
          hubble a s = hubble a t₀ *
            Real.sqrt (Ω * (a t₀ / a s) ^ 3 + (1 - Ω)))

/-- Item 4. Flat CPL dark-energy model as stated by Capozziello, Lazkoz and Salzano 2011.

Source (capozziello lines 11-21): `w = w₀ + wₐ (1 - a)` and
`E²(z) = Ω_m (1+z)³ + Ω_X (1+z)^{3(1+w₀+wₐ)} e^{-3 wₐ z/(1+z)}`, `Ω_X = 1 - Ω_m`, `E = H/H₀`,
`1 + z = a(t₀)/a(t)` (bamba line 25 for the redshift definition), `H = a'/a`.
`E²` is given, so I take `E = +√E²` with `H₀ > 0`, `a > 0` (source silent; expanding universe), and
impose the law near `t₀` (`∀ᶠ`), as in item 3. `z/(1+z) = 1 - a(t)/a(t₀)` is written that way.
Determined: truth of `P Ω w₀ wₐ a t₀` for all arguments; `Ω`, `w₀`, `wₐ` unrestricted (the real
power is of a positive base `1+z > 0`, so it is meaningful). -/
structure FlatCPLSpecG (P : ℝ → ℝ → ℝ → (ℝ → ℝ) → ℝ → Prop) : Prop where
  /-- Equivalence with `H(t) = H(t₀) √(E²)` near `t₀`, `E²` the printed formula of line 18-19. -/
  iff : ∀ (Ω w₀ wₐ : ℝ) (a : ℝ → ℝ) (t₀ : ℝ),
    P Ω w₀ wₐ a t₀ ↔
      (0 < a t₀ ∧ 0 < hubble a t₀ ∧
        ∀ᶠ s in nhds t₀, 0 < a s ∧ DifferentiableAt ℝ a s ∧
          hubble a s = hubble a t₀ *
            Real.sqrt (Ω * (a t₀ / a s) ^ (3 : ℝ) +
              (1 - Ω) * (a t₀ / a s) ^ (3 * (1 + w₀ + wₐ)) *
                Real.exp (-3 * wₐ * (1 - a s / a t₀))))

end Checked.Trust.SecondReadingSpecG


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

/-!
# Sourced blind specification readings G and H against four pinned definitions (run 2026-11-27T0428Z)

Same theorem names and shapes as `Checked/Trust/SpecAgreementCD.lean`: `meets_X_R : SpecR X` (the program's
definition is a model of reader R's specification) and `pins_X_R` (every function or condition meeting R's
specification equals / is equivalent to the program's, on R's domain), or `not_meets_X_R` with a witness.
Unlike readers C and D (run 2026-11-27T0228Z, memory only), readers G (Sonnet) and H (Opus) were handed
verbatim LaTeX excerpts of the three sources (`runs/2026-11-27T0428Z/sources/`).

Results:
* `curv` (Ricci scalar, Bamba et al. 2012 §XI): G and H AGREE (`meets_curv_G/H`, `pins_curv_G/H`). Both
  readers found the source's own inconsistency: §VIII.C writes `R = 6(Ḣ + 2H²)`, §XI (11.6) `R = −6(Ḣ + 2H²)`
  for the same metric; readers C and D (memory) had the §VIII sign.
* `curvK`: G AGREES; H DISAGREES (H reads the parameter as `Ω_K = −K/(H₀²a₀²)`, §X's named density
  parameter; the program's is the ratio `K/(H₀²a₀²)` printed in the coefficients, `= Ω₀ − 1`):
  `not_meets_curvK_H`, and H's specification determines minus the program's (`pins_neg_curvK_H`).
* `IsFlatLCDM`, `IsFlatCPL`: G AGREES for every argument (G, like the program, requires expansion at `t₀` and
  the law near `t₀`). H DISAGREES on contracting universes only (H does not require `H₀ > 0`; the
  contracting de Sitter universe meets H's condition, not the program's); H's condition is equivalent to the
  program's wherever `H₀ > 0` (`pins_IsFlatLCDM_H`, `pins_IsFlatCPL_H`). Both sourced readers read the law as
  holding near `t₀`, as the program does (reader D's all-times reading is not reproduced with the source).
-/

namespace Checked.Trust.SpecAgreement

open Filter Topology Real Checked.Cosmography Checked.Cosmography.Aviles Checked.Cosmography.BambaZ
open Checked.Cosmography.CPL Checked.Cosmography.FRCosmo
open Checked.Trust.SecondReadingSpecG Checked.Trust.SecondReadingSpecH

/-! ## Ricci scalar (§XI sign): both sourced readers agree -/

theorem meets_curv_G : RicciFlatSpecG curv :=
  ⟨fun _ _ _ _ _ => rfl⟩

theorem pins_curv_G (R : (ℝ → ℝ) → ℝ → ℝ) (h : RicciFlatSpecG R) (a : ℝ → ℝ) (t : ℝ) (ha : a t ≠ 0)
    (h1 : ∀ᶠ s in nhds t, DifferentiableAt ℝ a s) (h2 : DifferentiableAt ℝ (deriv a) t) :
    R a t = curv a t := by
  rw [h.formula a t ha h1 h2, meets_curv_G.formula a t ha h1 h2]

theorem meets_curv_H : RicciFlatSpecH curv :=
  ⟨fun _ _ _ _ _ => rfl⟩

theorem pins_curv_H (R : (ℝ → ℝ) → ℝ → ℝ) (h : RicciFlatSpecH R) (a : ℝ → ℝ) (t : ℝ) (ha : 0 < a t)
    (h1 : ∀ᶠ s in nhds t, DifferentiableAt ℝ a s) (h2 : DifferentiableAt ℝ (deriv a) t) :
    R a t = curv a t := by
  rw [h.formula a t ha h1 h2, meets_curv_H.formula a t ha h1 h2]

/-! ## Curvature parameter -/

theorem meets_curvK_G : CurvParamSpecG curvK :=
  ⟨fun K a t₀ _ _ => by unfold curvK Checked.Cosmography.hubble; ring⟩

theorem pins_curvK_G (k : ℝ → (ℝ → ℝ) → ℝ → ℝ) (h : CurvParamSpecG k) (K : ℝ) (a : ℝ → ℝ) (t₀ : ℝ)
    (ha : a t₀ ≠ 0) (hd : deriv a t₀ ≠ 0) : k K a t₀ = curvK K a t₀ := by
  rw [h.formula K a t₀ ha hd, meets_curvK_G.formula K a t₀ ha hd]

/-- **Disagreement (proved):** for `K = 1`, `a = exp`, `t₀ = 0` the program's parameter is `1`, reader H's `−1`. -/
theorem not_meets_curvK_H : ¬ CurvParamSpecH curvK := by
  intro h
  have e := h.formula 1 Real.exp 0 (Real.exp_pos 0) (by rw [Real.deriv_exp]; exact (Real.exp_pos 0).ne')
  unfold curvK Checked.Cosmography.hubble at e
  rw [Real.deriv_exp] at e
  have h0 : Real.exp 0 ≠ 0 := (Real.exp_pos 0).ne'
  field_simp at e
  norm_num at e

/-- Reader H's specification determines minus the program's curvature parameter. -/
theorem pins_neg_curvK_H (k : ℝ → (ℝ → ℝ) → ℝ → ℝ) (h : CurvParamSpecH k) (K : ℝ) (a : ℝ → ℝ) (t₀ : ℝ)
    (ha : 0 < a t₀) (hd : deriv a t₀ ≠ 0) : k K a t₀ = -curvK K a t₀ := by
  rw [h.formula K a t₀ ha hd]
  unfold curvK Checked.Cosmography.hubble
  ring

/-! ## Flat ΛCDM and flat CPL model conditions -/

lemma lcdm_radicand (Ω x : ℝ) : Ω * (1 + (x - 1)) ^ 3 + 1 - Ω = Ω * x ^ 3 + (1 - Ω) := by ring

theorem meets_IsFlatLCDM_G : FlatLCDMSpecG IsFlatLCDM := by
  refine ⟨fun Ω a t₀ => ?_⟩
  unfold IsFlatLCDM redshift
  simp only [Checked.Cosmography.hubble, Checked.Trust.SecondReadingSpecG.hubble, lcdm_radicand]
  constructor
  · rintro ⟨hH, ev⟩
    exact ⟨ev.self_of_nhds.1, hH, ev⟩
  · rintro ⟨_, hH, ev⟩
    exact ⟨hH, ev⟩

theorem pins_IsFlatLCDM_G (P : ℝ → (ℝ → ℝ) → ℝ → Prop) (h : FlatLCDMSpecG P) (Ω : ℝ) (a : ℝ → ℝ)
    (t₀ : ℝ) : P Ω a t₀ ↔ IsFlatLCDM Ω a t₀ := by
  rw [h.iff, meets_IsFlatLCDM_G.iff]

lemma cpl_radicand (Ω w₀ wₐ : ℝ) (x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) :
    Ω * (1 + (y / x - 1)) ^ 3 + (1 - Ω) * (1 + (y / x - 1)) ^ (3 * (1 + w₀ + wₐ)) *
      Real.exp (-(3 * wₐ * (y / x - 1)) / (1 + (y / x - 1))) =
    Ω * (y / x) ^ (3 : ℝ) + (1 - Ω) * (y / x) ^ (3 * (1 + w₀ + wₐ)) *
      Real.exp (-3 * wₐ * (1 - x / y)) := by
  rw [show 1 + (y / x - 1) = y / x by ring, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num,
    Real.rpow_natCast]
  congr 3
  field_simp

theorem meets_IsFlatCPL_G : FlatCPLSpecG IsFlatCPL := by
  refine ⟨fun Ω w₀ wₐ a t₀ => ?_⟩
  unfold IsFlatCPL redshift
  simp only [Checked.Cosmography.hubble, Checked.Trust.SecondReadingSpecG.hubble]
  constructor
  · rintro ⟨hH, ev⟩
    have h0 := ev.self_of_nhds.1
    exact ⟨h0, hH, ev.mono fun t ⟨p, d, q⟩ => ⟨p, d, by
      rw [q, cpl_radicand Ω w₀ wₐ (a t) (a t₀) p.ne' h0.ne']⟩⟩
  · rintro ⟨h0, hH, ev⟩
    exact ⟨hH, ev.mono fun t ⟨p, d, q⟩ => ⟨p, d, by
      rw [q, cpl_radicand Ω w₀ wₐ (a t) (a t₀) p.ne' h0.ne']⟩⟩

theorem pins_IsFlatCPL_G (P : ℝ → ℝ → ℝ → (ℝ → ℝ) → ℝ → Prop) (h : FlatCPLSpecG P) (Ω w₀ wₐ : ℝ)
    (a : ℝ → ℝ) (t₀ : ℝ) : P Ω w₀ wₐ a t₀ ↔ IsFlatCPL Ω w₀ wₐ a t₀ := by
  rw [h.iff, meets_IsFlatCPL_G.iff]

/-! Reader H: the law written as `HasDerivAt a (a t * (H₀ * √…)) t` near `t₀`, no sign condition on `H₀`. -/

/-- Generic bridge: near `t₀`, "`a` has derivative `a t * (H₀ * F t)`" is "`a > 0`, differentiable, and
`a'/a = H₀ * F t`", given `a t₀ > 0`. -/
lemma hasDeriv_iff_hubble (a F : ℝ → ℝ) (t₀ H₀ : ℝ) (ha : 0 < a t₀) :
    (∀ᶠ t in nhds t₀, HasDerivAt a (a t * (H₀ * F t)) t) ↔
      ∀ᶠ t in nhds t₀, 0 < a t ∧ DifferentiableAt ℝ a t ∧ deriv a t / a t = H₀ * F t := by
  constructor
  · intro ev
    have hc : ContinuousAt a t₀ := ev.self_of_nhds.continuousAt
    have hpos : ∀ᶠ t in nhds t₀, 0 < a t := hc.eventually (lt_mem_nhds ha)
    filter_upwards [ev, hpos] with t hd hp
    refine ⟨hp, hd.differentiableAt, ?_⟩
    rw [hd.deriv]
    field_simp
  · intro ev
    filter_upwards [ev] with t ⟨hp, hd, hq⟩
    have : deriv a t = a t * (H₀ * F t) := by
      rw [← hq]; field_simp
    rw [← this]
    exact hd.hasDerivAt

lemma hasDerivAt_expNeg' (t : ℝ) :
    HasDerivAt (fun s => Real.exp (-s)) (-Real.exp (-t)) t := by
  have := (hasDerivAt_neg t).exp
  convert this using 1; ring

lemma hubble_expNeg' (t : ℝ) : deriv (fun s => Real.exp (-s)) t / Real.exp (-t) = -1 := by
  rw [(hasDerivAt_expNeg' t).deriv]; field_simp

/-- **Disagreement (proved):** the contracting de Sitter universe `a = e^{−t}`, `Ω = 0`, meets reader H's flat
ΛCDM condition at `t₀ = 0`, not the program's (which requires expansion at `t₀`). -/
theorem not_meets_IsFlatLCDM_H : ¬ FlatLCDMSpecH IsFlatLCDM := by
  intro h
  have hd : deriv (fun s => Real.exp (-s)) 0 ≠ 0 := by
    rw [(hasDerivAt_expNeg' 0).deriv]; simp
  have hc := (h.iff 0 (fun s => Real.exp (-s)) 0 (Real.exp_pos _) hd).2 (Eventually.of_forall fun t => by
    have e : Real.exp (-t) * (deriv (fun s => Real.exp (-s)) 0 / Real.exp (-0) *
        Real.sqrt (0 * (Real.exp (-0) / Real.exp (-t)) ^ (3 : ℕ) + 1 - 0)) = -Real.exp (-t) := by
      rw [hubble_expNeg']; simp
    rw [e]; exact hasDerivAt_expNeg' t)
  have := hc.1
  unfold Checked.Cosmography.hubble at this
  rw [hubble_expNeg'] at this
  norm_num at this

theorem pins_IsFlatLCDM_H (P : ℝ → (ℝ → ℝ) → ℝ → Prop) (h : FlatLCDMSpecH P) (Ω : ℝ) (a : ℝ → ℝ)
    (t₀ : ℝ) (ha : 0 < a t₀) (hH : 0 < deriv a t₀ / a t₀) : P Ω a t₀ ↔ IsFlatLCDM Ω a t₀ := by
  have hd : deriv a t₀ ≠ 0 := fun e => by rw [e, zero_div] at hH; exact lt_irrefl 0 hH
  rw [h.iff Ω a t₀ ha hd, hasDeriv_iff_hubble a _ t₀ _ ha]
  unfold IsFlatLCDM redshift
  simp only [Checked.Cosmography.hubble, lcdm_radicand]
  constructor
  · intro ev
    exact ⟨hH, ev.mono fun t ⟨p, d, q⟩ => ⟨p, d, by rw [q]; ring_nf⟩⟩
  · rintro ⟨_, ev⟩
    exact ev.mono fun t ⟨p, d, q⟩ => ⟨p, d, by rw [q]; ring_nf⟩

/-- **Disagreement (proved):** the same contracting universe (`Ω = 0`, `w₀ = −1`, `wₐ = 0`) meets reader H's
flat CPL condition, not the program's. -/
theorem not_meets_IsFlatCPL_H : ¬ FlatCPLSpecH IsFlatCPL := by
  intro h
  have hd : deriv (fun s => Real.exp (-s)) 0 ≠ 0 := by
    rw [(hasDerivAt_expNeg' 0).deriv]; simp
  have hc := (h.iff 0 (-1) 0 (fun s => Real.exp (-s)) 0 (Real.exp_pos _) hd).2
    (Eventually.of_forall fun t => by
      have e : Real.exp (-t) * (deriv (fun s => Real.exp (-s)) 0 / Real.exp (-0) *
          Real.sqrt (0 * (Real.exp (-0) / Real.exp (-t)) ^ (3 : ℕ) + (1 - 0) *
            (Real.exp (-0) / Real.exp (-t)) ^ (3 * (1 + (-1) + 0) : ℝ) *
              Real.exp (-(3 * 0 * (Real.exp (-0) / Real.exp (-t) - 1)) /
                (Real.exp (-0) / Real.exp (-t))))) = -Real.exp (-t) := by
        rw [hubble_expNeg']; norm_num
      rw [e]; exact hasDerivAt_expNeg' t)
  have := hc.1
  unfold Checked.Cosmography.hubble at this
  rw [hubble_expNeg'] at this
  norm_num at this

lemma cpl_radicand_H (Ω w₀ wₐ : ℝ) (x y : ℝ) :
    Ω * (1 + (y / x - 1)) ^ 3 + (1 - Ω) * (1 + (y / x - 1)) ^ (3 * (1 + w₀ + wₐ)) *
      Real.exp (-(3 * wₐ * (y / x - 1)) / (1 + (y / x - 1))) =
    Ω * (y / x) ^ (3 : ℕ) + (1 - Ω) * (y / x) ^ (3 * (1 + w₀ + wₐ)) *
      Real.exp (-(3 * wₐ * (y / x - 1)) / (y / x)) := by
  rw [show 1 + (y / x - 1) = y / x by ring]

theorem pins_IsFlatCPL_H (P : ℝ → ℝ → ℝ → (ℝ → ℝ) → ℝ → Prop) (h : FlatCPLSpecH P) (Ω w₀ wₐ : ℝ)
    (a : ℝ → ℝ) (t₀ : ℝ) (ha : 0 < a t₀) (hH : 0 < deriv a t₀ / a t₀) :
    P Ω w₀ wₐ a t₀ ↔ IsFlatCPL Ω w₀ wₐ a t₀ := by
  have hd : deriv a t₀ ≠ 0 := fun e => by rw [e, zero_div] at hH; exact lt_irrefl 0 hH
  rw [h.iff Ω w₀ wₐ a t₀ ha hd, hasDeriv_iff_hubble a _ t₀ _ ha]
  unfold IsFlatCPL redshift
  simp only [Checked.Cosmography.hubble, cpl_radicand_H]
  constructor
  · intro ev
    exact ⟨hH, ev⟩
  · rintro ⟨_, ev⟩
    exact ev

end Checked.Trust.SpecAgreement
