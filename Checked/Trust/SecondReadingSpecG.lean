/- Copied verbatim (code unchanged) from `runs/2026-11-27T0428Z/specG/SecondReadingSpecG.lean`, written by blind reader G (Sonnet subagent, brief `runs/2026-11-27T0428Z/specG/briefG.md`; handed verbatim LaTeX excerpts of the three sources, `runs/2026-11-27T0428Z/sources/`, and read only those). Agreement with the program's pinned definitions: `Checked/Trust/SpecAgreementGH.lean`. -/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp

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
