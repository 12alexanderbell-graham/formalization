import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
Blind reading K of Bamba, Capozziello, Nojiri, Odintsov, arXiv:1205.3421v3, section XI
("An example: testing F(R) gravity by cosmography"). Line numbers below refer to the source
file `ED1-32.tex` as transcribed in `sources/bamba2012_1205.3421v3.md`.

Conventions: c = 1, kappa^2 = 1, `a` the flat FLRW scale factor as a function of cosmic time
(not normalised to one at `t₀`), `Ω` the present matter density parameter `Ω_M^{(0)}`.
-/

namespace Checked.Trust.SecondReadingSpecK

/-- The Hubble rate of the flat FLRW scale factor `a`: `H(t) = ȧ(t) / a(t)`.
Source: the excerpt does not print the definition; the standard one is used (section XI, line 159
and the Friedmann form at lines 83–84 use this `H`). Choice made by this reading. -/
noncomputable def hubbleRateK (a : ℝ → ℝ) (t : ℝ) : ℝ :=
  deriv a t / a t

/-- The scalar curvature as section XI writes it through the Hubble rate:
`R(t) = -6 (Ḣ(t) + 2 H(t)^2)`, with `Ḣ = deriv (hubbleRateK a)`.
Source: section XI, line 163 (eq. rvsh). Note the sign: section VIII, lines 7316 and 7515, writes
`R = +6 (Ḣ + 2H^2)`. This reading follows section XI as printed, per the brief. -/
noncomputable def ricciScalarK (a : ℝ → ℝ) (t : ℝ) : ℝ :=
  -6 * (deriv (hubbleRateK a) t + 2 * hubbleRateK a t ^ 2)

/-- The matter density as section XI gives it: `ρ_M(t) = ρ_M(t₀) (a(t₀)/a(t))^3` with
`ρ_M(t₀) = 3 H₀² Ω`, `H₀ = H(t₀)`. Source: section XI, line 105, `ρ_M = ρ_M(t=t₀) a^{-3} = 3 H₀² Ω_M a^{-3}`,
written there for `a(t₀) = 1`; the factor `(a(t₀)/a(t))^3` is this reading's generalisation to a
scale factor not normalised at `t₀` (choice made here, see `DustDensitySpecK`). -/
noncomputable def matterDensityK (Ω : ℝ) (a : ℝ → ℝ) (t₀ t : ℝ) : ℝ :=
  3 * hubbleRateK a t₀ ^ 2 * Ω * (a t₀ / a t) ^ 3

/-- The energy density of the effective curvature fluid, section XI, line 97 (eq. rhocurv):
`ρ_curv = (1/F'(R)) [ (1/2)(F(R) - R F'(R)) - 3 H Ṙ F''(R) ]`, with `R = ricciScalarK a t`,
`F' = deriv F`, `F'' = deriv (deriv F)`, `Ṙ = deriv (ricciScalarK a) t`. -/
noncomputable def rhoCurvK (F : ℝ → ℝ) (a : ℝ → ℝ) (t : ℝ) : ℝ :=
  (1 / deriv F (ricciScalarK a t)) *
    ((1 / 2) * (F (ricciScalarK a t) - ricciScalarK a t * deriv F (ricciScalarK a t))
      - 3 * hubbleRateK a t * deriv (ricciScalarK a) t * deriv (deriv F) (ricciScalarK a t))

/-- Specification of the matter energy density `ρ Ω a t₀ t` of section XI.

Determines: `ρ Ω a t₀ t` for all `Ω`, `a`, `t₀`, `t` with `0 < a t₀`, `0 < a t`, and `a`
differentiable at `t₀` (the Hubble rate at `t₀` must be defined). Outside those arguments nothing
is constrained.

Fields:
* `scaling` — the matter continuity law `ρ_M(t) = ρ_M(t₀) (a(t₀)/a(t))^3`. Source: section XI,
  line 104–105 (`ρ_M = ρ_M(t=t₀) a^{-3}`). Choice: the source writes `a^{-3}` with `a(t₀) = 1`; the
  ratio `a(t₀)/a(t)` is used so that the law holds for a scale factor not normalised at `t₀`.
* `present` — the present matter density `ρ_M(t₀) = 3 H₀² Ω`. Source: section XI, line 105
  (`ρ_M(t=t₀) = 3 H₀² Ω_M^{(0)}`), with `κ² = 1` (line 91). `H₀ = H(t₀) = ȧ(t₀)/a(t₀)`. -/
structure DustDensitySpecK (ρ : ℝ → (ℝ → ℝ) → ℝ → ℝ → ℝ) : Prop where
  /-- Matter continuity scaling (section XI, lines 104–105):
  for `0 < a t₀` and `0 < a t`, `ρ Ω a t₀ t = ρ Ω a t₀ t₀ * (a t₀ / a t)^3`. -/
  scaling : ∀ (Ω : ℝ) (a : ℝ → ℝ) (t₀ t : ℝ),
    0 < a t₀ → 0 < a t → ρ Ω a t₀ t = ρ Ω a t₀ t₀ * (a t₀ / a t) ^ 3
  /-- Present matter density (section XI, line 105, with `κ² = 1`, line 91):
  for `0 < a t₀` and `a` differentiable at `t₀`, `ρ Ω a t₀ t₀ = 3 * H(t₀)^2 * Ω`, where
  `H(t₀) = deriv a t₀ / a t₀`. -/
  present : ∀ (Ω : ℝ) (a : ℝ → ℝ) (t₀ : ℝ),
    0 < a t₀ → DifferentiableAt ℝ a t₀ → ρ Ω a t₀ t₀ = 3 * hubbleRateK a t₀ ^ 2 * Ω

/-- Specification of the statement "the Friedmann equation of F(R) gravity holds at time `t`"
(section XI, line 83–84, eq. hfr):
`H^2 = (1/3) (ρ_M / F'(R) + ρ_curv)`, with `κ² = 1`, `R = ricciScalarK a t`, `ρ_M = matterDensityK Ω a t₀ t`,
`ρ_curv = rhoCurvK F a t`.

Side conditions under which the equation is read (choices of this reading, required for the
quantities to be defined as the source uses them): `0 < a t₀`, `a` differentiable at `t₀`,
`0 < a s` and `a` of class C^3 at `s` for `s` near `t` (so that `H`, `Ṙ` exist near `t`),
`F` of class C^2 at `R(t)` (so that `F''` exists there), and `F'(R(t)) ≠ 0` (the equation divides by
`F'`). Under these conditions the spec determines `P Ω a F t₀ t`. Nothing is constrained where a side
condition fails.

Fields:
* `iff` — `P Ω a F t₀ t ↔ H(t)^2 = (1/3) (ρ_M / F'(R) + ρ_curv)` under the side conditions above. -/
structure FRFriedmannSpecK (P : ℝ → (ℝ → ℝ) → (ℝ → ℝ) → ℝ → ℝ → Prop) : Prop where
  /-- For all `Ω a F t₀ t` satisfying the side conditions (`0 < a t₀`, `DifferentiableAt ℝ a t₀`,
  eventually `0 < a s ∧ ContDiffAt ℝ 3 a s` near `t`, `ContDiffAt ℝ 2 F (R t)`, `deriv F (R t) ≠ 0`):
  `P Ω a F t₀ t ↔ hubbleRateK a t ^ 2 = 1/3 * (matterDensityK Ω a t₀ t / deriv F (ricciScalarK a t) + rhoCurvK F a t)`.
  Source: section XI, lines 83–84 and 97. -/
  iff : ∀ (Ω : ℝ) (a F : ℝ → ℝ) (t₀ t : ℝ),
    0 < a t₀ → DifferentiableAt ℝ a t₀ →
    (∀ᶠ s in nhds t, 0 < a s ∧ ContDiffAt ℝ 3 a s) →
    ContDiffAt ℝ 2 F (ricciScalarK a t) →
    deriv F (ricciScalarK a t) ≠ 0 →
    (P Ω a F t₀ t ↔
      hubbleRateK a t ^ 2 =
        1 / 3 * (matterDensityK Ω a t₀ t / deriv F (ricciScalarK a t) + rhoCurvK F a t))

/-- Specification of the statement "the master equation for the Hubble parameter of F(R) gravity
holds at time `t`" (section XI, lines 148–157, eq. presingleeq):
`Ḣ = -(1/(2 F'(R))) [ 3 H₀² Ω a^{-3} + R̈ F''(R) + Ṙ (Ṙ F'''(R) - H F''(R)) ]`,
where `3 H₀² Ω a^{-3}` is `matterDensityK Ω a t₀ t`, `R = ricciScalarK a t` (section XI, line 163).

Side conditions under which the equation is read: `0 < a t₀`, `a` differentiable at `t₀`, eventually
near `t`: `0 < a s` and `a` of class C^4 at `s` (so that `Ḣ`, `Ṙ`, `R̈` exist near `t`), `F` of class C^3
at `R(t)` eventually near `R(t)` (so that `F'''` exists), and `F'(R(t)) ≠ 0` (the equation divides by `F'`).
Under these conditions the spec determines `P Ω a F t₀ t`; nothing is constrained where a side condition
fails.

Fields:
* `iff` — `P Ω a F t₀ t ↔ Ḣ(t) = -(1/(2 F'(R))) [ ... ]` under the side conditions above. -/
structure FRMasterSpecK (P : ℝ → (ℝ → ℝ) → (ℝ → ℝ) → ℝ → ℝ → Prop) : Prop where
  /-- For all `Ω a F t₀ t` satisfying the side conditions (`0 < a t₀`, `DifferentiableAt ℝ a t₀`,
  eventually `0 < a s ∧ ContDiffAt ℝ 4 a s` near `t`, eventually `ContDiffAt ℝ 3 F y` near `R t`,
  `deriv F (R t) ≠ 0`):
  `P Ω a F t₀ t ↔ deriv (hubbleRateK a) t =
     -(1 / (2 * deriv F (R t))) * (matterDensityK Ω a t₀ t + R̈ * F''(R t)
        + Ṙ * (Ṙ * F'''(R t) - H t * F''(R t)))`,
  with `R̈ = deriv (deriv (ricciScalarK a)) t`, `Ṙ = deriv (ricciScalarK a) t`,
  `F'' = deriv (deriv F)`, `F''' = deriv (deriv (deriv F))`.
  Source: section XI, lines 148–157 (eq. presingleeq). -/
  iff : ∀ (Ω : ℝ) (a F : ℝ → ℝ) (t₀ t : ℝ),
    0 < a t₀ → DifferentiableAt ℝ a t₀ →
    (∀ᶠ s in nhds t, 0 < a s ∧ ContDiffAt ℝ 4 a s) →
    (∀ᶠ y in nhds (ricciScalarK a t), ContDiffAt ℝ 3 F y) →
    deriv F (ricciScalarK a t) ≠ 0 →
    (P Ω a F t₀ t ↔
      deriv (hubbleRateK a) t =
        -(1 / (2 * deriv F (ricciScalarK a t))) *
          (matterDensityK Ω a t₀ t
            + deriv (deriv (ricciScalarK a)) t * deriv (deriv F) (ricciScalarK a t)
            + deriv (ricciScalarK a) t *
                (deriv (ricciScalarK a) t * deriv (deriv (deriv F)) (ricciScalarK a t)
                  - hubbleRateK a t * deriv (deriv F) (ricciScalarK a t))))

end Checked.Trust.SecondReadingSpecK
