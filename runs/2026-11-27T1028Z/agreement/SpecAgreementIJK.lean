import Checked.Cosmography.FRCosmo
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
Blind specification reading I of Bamba-Capozziello-Nojiri-Odintsov, arXiv:1205.3421v3, section XI
(source file `bamba2012_1205.3421v3.md`, line numbers below are of that file).
-/

namespace Checked.Trust.SecondReadingSpecI

/-- Hubble rate of the scale factor `a` (not normalised): `H = a'/a` (source lines 83-85 use `H` as the
expansion rate; the formula `a'/a` is the standard definition, the source does not print it). -/
noncomputable def hubble (a : ℝ → ℝ) (t : ℝ) : ℝ := deriv a t / a t

/-- Ricci scalar as section XI writes it through the Hubble rate, line 163:
`R = -6 (Hdot + 2 H^2)` (sign as printed in XI; section VIII.C, lines 7317/7319 prints `+6`). -/
noncomputable def ricci (a : ℝ → ℝ) (t : ℝ) : ℝ :=
  -6 * (deriv (hubble a) t + 2 * (hubble a t) ^ 2)

/-- Matter density of section XI (lines 104-106) for a scale factor not normalised at `t₀`:
`ρ_M = ρ_M(t₀) (a(t₀)/a(t))^3`, with `ρ_M(t₀) = 3 H₀² Ω`, `H₀ = a'(t₀)/a(t₀)`. -/
noncomputable def dustForm (Ω : ℝ) (a : ℝ → ℝ) (t₀ t : ℝ) : ℝ :=
  3 * (hubble a t₀) ^ 2 * Ω * (a t₀ / a t) ^ 3

/-- Effective curvature fluid density, line 97-98, with `Rdot = d/dt (ricci a)`:
`ρ_curv = (1/F'(R)) [ (F(R) - R F'(R))/2 - 3 H Rdot F''(R) ]`. -/
noncomputable def rhoCurv (a F : ℝ → ℝ) (t : ℝ) : ℝ :=
  (1 / deriv F (ricci a t)) *
    ((F (ricci a t) - ricci a t * deriv F (ricci a t)) / 2
      - 3 * hubble a t * deriv (ricci a) t * deriv (deriv F) (ricci a t))

/-- The matter density `ρ Ω a t₀ t` of section XI (lines 104-106): units `κ² = 1` (line 91), `c = 1`,
`ρ_M(t₀) = 3 H₀² Ω` where `Ω = Ω_M^{(0)}` and `H₀ = a'(t₀)/a(t₀)`, and continuity (no interaction in the
Jordan frame, lines 102-104) gives `ρ_M ∝ a^{-3}`. The source takes `a(t₀)=1`; for a general scale factor
the scaling is written `(a(t₀)/a(t))^3` (my generalisation, the only choice consistent with `a^{-3}` when
`a(t₀)=1`). Determined: all `Ω`, `t₀`, `t` and `a` with `a t₀ > 0`, `a t > 0` (the notion is meaningful
for a positive scale factor; nothing is asserted otherwise). -/
structure DustDensitySpecI (ρ : ℝ → (ℝ → ℝ) → ℝ → ℝ → ℝ) : Prop where
  /-- Present value (lines 104-105): `ρ_M(t = t₀) = 3 H₀² Ω` with `H₀ = a'(t₀)/a(t₀)`. -/
  present : ∀ (Ω : ℝ) (a : ℝ → ℝ) (t₀ : ℝ), 0 < a t₀ →
    ρ Ω a t₀ t₀ = 3 * (deriv a t₀ / a t₀) ^ 2 * Ω
  /-- Scaling `ρ_M ∝ a^{-3}` (line 104): `ρ(t) a(t)^3 = ρ(t₀) a(t₀)^3` (continuity equation of dust). -/
  scaling : ∀ (Ω : ℝ) (a : ℝ → ℝ) (t₀ t : ℝ), 0 < a t₀ → 0 < a t →
    ρ Ω a t₀ t * (a t) ^ 3 = ρ Ω a t₀ t₀ * (a t₀) ^ 3

/-- Section XI Friedmann equation (line 83, `κ² = 1`):
`H² = (1/3) (ρ_M / F'(R) + ρ_curv)` with `ρ_curv` of lines 97-98, `R = -6(Hdot + 2H²)` (line 163),
`ρ_M = dustForm` (lines 104-106). Determined: truth of the equation for every `Ω, a, F, t₀, t` with
`F'(R(t)) ≠ 0` (where the source divides by `F'`). Derivatives are Mathlib `deriv` of explicit functions
of time; no differentiability hypotheses are added (the source states none), so at points where a
derivative fails to exist the equation is read with Mathlib's junk value `0`. Nothing is asserted when
`F'(R) = 0`. -/
structure FRFriedmannSpecI
    (P : ℝ → (ℝ → ℝ) → (ℝ → ℝ) → ℝ → ℝ → Prop) : Prop where
  /-- `P ↔ H² = (1/3)(ρ_M/F'(R) + ρ_curv)` (line 83) when `F'(R(t)) ≠ 0` and `a t₀ > 0`, `a t > 0`. -/
  iff_eq : ∀ (Ω : ℝ) (a F : ℝ → ℝ) (t₀ t : ℝ), 0 < a t₀ → 0 < a t → deriv F (ricci a t) ≠ 0 →
    (P Ω a F t₀ t ↔
      (hubble a t) ^ 2 =
        (1 / 3) * (dustForm Ω a t₀ t / deriv F (ricci a t) + rhoCurv a F t))

/-- Section XI master equation (lines 149-156), `κ² = 1`:
`Hdot = -(1/(2F'(R))) [ 3 H₀² Ω a^{-3} + Rddot F''(R) + Rdot (Rdot F'''(R) - H F''(R)) ]`,
with `R = -6(Hdot + 2H²)` (line 163), `Rdot = d/dt R`, `Rddot = d²/dt² R`, the matter term being
`dustForm` (not normalised `a`). Determined: truth for every `Ω, a, F, t₀, t` with `F'(R(t)) ≠ 0`,
`a t₀ > 0`, `a t > 0`. Mathlib junk-value convention for non-existent derivatives, as above. -/
structure FRMasterSpecI
    (P : ℝ → (ℝ → ℝ) → (ℝ → ℝ) → ℝ → ℝ → Prop) : Prop where
  /-- `P ↔ Hdot = -(1/(2F'))[ρ_M + R̈F'' + Ṙ(ṘF''' - HF'')]` (line 149-155). -/
  iff_eq : ∀ (Ω : ℝ) (a F : ℝ → ℝ) (t₀ t : ℝ), 0 < a t₀ → 0 < a t → deriv F (ricci a t) ≠ 0 →
    (P Ω a F t₀ t ↔
      deriv (hubble a) t =
        -(1 / (2 * deriv F (ricci a t))) *
          (dustForm Ω a t₀ t
            + deriv (deriv (ricci a)) t * deriv (deriv F) (ricci a t)
            + deriv (ricci a) t *
                (deriv (ricci a) t * deriv (deriv (deriv F)) (ricci a t)
                  - hubble a t * deriv (deriv F) (ricci a t))))

end Checked.Trust.SecondReadingSpecI


/-!
# Blind specification reading J: three items of section XI of Bamba–Capozziello–Nojiri–Odintsov 2012

Source: `sources/bamba2012_1205.3421v3.md` (verbatim excerpts of `ED1-32.tex` of arXiv:1205.3421v3).
All line numbers below are line numbers of that excerpt file (each is followed, where useful, by the
corresponding LaTeX label).

Conventions fixed by section XI (excerpt lines 70–179):
* `c = 1`, gravitational coupling `κ² = 1` (line 91).
* Spatially flat FLRW scale factor `a`, Hubble rate `H = ȧ / a` (standard; the source never spells it out
  in the excerpts, it only writes `H`, `H_0`).
* Ricci scalar **as section XI prints it**: `R = -6 (Ḣ + 2 H²)` (lines 162–165, label `eq: rvsh`).
  Note that §VIII uses the opposite sign `R = 6 (Ḣ + 2 H²)` (lines 32, 35); following the brief we use
  the section XI sign.
* Primes on `F` are derivatives with respect to `R` (line 88), dots are cosmic-time derivatives.
* `H_0 = H(t₀)`; since the scale factor is not normalised to one at `t₀`, the source's `a^{-3}`
  (lines 104–105, 112, 150, written for `a(t₀) = 1`, cf. line 25 `a_0 = 1`) is read as `(a(t₀)/a(t))³`.
-/

namespace Checked.Trust.SecondReadingSpecJ

/-- **Item 1: matter (dust) energy density of section XI.**

`ρ Ω a t₀ t` is the matter energy density at time `t` (units `c = 1`, `κ² = 1`, line 91), for present
matter density parameter `Ω` and present time `t₀`, with a scale factor `a` not normalised at `t₀`.

Source: lines 102–106: "the matter continuity equation gives the usual scaling
`ρ_M = ρ_M(t = t_0) a^{-3} = 3 H_0^2 Ω_M a^{-3}`". The two fields below are exactly these two
statements, rewritten for an un-normalised scale factor: the dust scaling `ρ_M a³ = const` and the
present value `ρ_M(t₀) = 3 H_0² Ω`.

Determination: the two fields together fix `ρ Ω a t₀ t = 3 H_0² Ω (a(t₀)/a(t))³` (with
`H_0 = ȧ(t₀)/a(t₀)`, Mathlib `deriv`) for every `Ω`, `a`, `t₀`, `t` with `a t ≠ 0` and `a t₀ ≠ 0`. Nothing
is said where `a` vanishes (there `H_0` or `a^{-3}` is undefined). Choice (source silent): no
differentiability hypothesis on `a` at `t₀`; `H_0` is read as Mathlib's `deriv a t₀ / a t₀`. -/
structure DustDensitySpecJ (ρ : ℝ → (ℝ → ℝ) → ℝ → ℝ → ℝ) : Prop where
  /-- Present value (lines 104–106): `ρ_M(t₀) = 3 H_0² Ω_M` with `H_0 = H(t₀) = ȧ(t₀)/a(t₀)` the present
  Hubble rate; this is the definition of the matter density parameter with `κ² = 1` (line 91).
  Hypothesis `a t₀ ≠ 0` so that `H_0` is defined. -/
  present_value : ∀ (Ω : ℝ) (a : ℝ → ℝ) (t₀ : ℝ), a t₀ ≠ 0 →
    ρ Ω a t₀ t₀ = 3 * (deriv a t₀ / a t₀) ^ 2 * Ω
  /-- Dust scaling (lines 102–105, "the matter continuity equation gives the usual scaling
  `ρ_M = ρ_M(t = t_0) a^{-3}`"), written for a non-normalised scale factor as
  `ρ_M(t) a(t)³ = ρ_M(t₀) a(t₀)³`. Hypotheses `a t ≠ 0`, `a t₀ ≠ 0` (where `a^{-3}` is defined). -/
  dust_scaling : ∀ (Ω : ℝ) (a : ℝ → ℝ) (t₀ t : ℝ), a t ≠ 0 → a t₀ ≠ 0 →
    ρ Ω a t₀ t * a t ^ 3 = ρ Ω a t₀ t₀ * a t₀ ^ 3

/-- **Item 2: the Friedmann equation of F(R) gravity in the form section XI prints it.**

Lines 82–86 (label `eq: hfr`): `H² = (1/3) (ρ_M / F'(R) + ρ_curv)`, with `κ² = 1` (line 91),
`ρ_curv = (1/F'(R)) [ (F(R) - R F'(R))/2 - 3 H Ṙ F''(R) ]` (lines 96–100, label `eq: rhocurv`),
`ρ_M = 3 H_0² Ω a^{-3}` (line 105, read as `3 H_0² Ω (a(t₀)/a(t))³` for a non-normalised `a`),
`R = -6 (Ḣ + 2 H²)` (line 163, section XI's sign), `H = ȧ/a`, `H_0 = H(t₀)`.

Determination: the truth of `P Ω a F t₀ t` is fixed for every `Ω`, `a`, `F`, `t₀`, `t` with `a t ≠ 0`,
`a t₀ ≠ 0` and `F'(R(t)) ≠ 0` (the quantities the source divides by). Choice (source silent): no
smoothness hypotheses on `a` or `F`; all derivatives are Mathlib's `deriv`. -/
structure FRFriedmannSpecJ (P : ℝ → (ℝ → ℝ) → (ℝ → ℝ) → ℝ → ℝ → Prop) : Prop where
  /-- The equation of lines 82–86 written out literally, with `ρ_curv` of lines 96–100 inlined:
  `H(t)² = (1/3) ( ρ_M(t)/F'(R(t)) + (1/F'(R(t))) [ (F(R(t)) - R(t) F'(R(t)))/2
  - 3 H(t) Ṙ(t) F''(R(t)) ] )`, where `H(s) = ȧ(s)/a(s)`, `R(s) = -6 (Ḣ(s) + 2 H(s)²)` (line 163),
  `Ṙ` is `deriv` of the explicit function `s ↦ R(s)`, `ρ_M(t) = 3 (ȧ(t₀)/a(t₀))² Ω (a(t₀)/a(t))³`
  (line 105). Side conditions: `a t ≠ 0`, `a t₀ ≠ 0`, `F'(R(t)) ≠ 0`. -/
  iff_friedmann : ∀ (Ω : ℝ) (a F : ℝ → ℝ) (t₀ t : ℝ), a t ≠ 0 → a t₀ ≠ 0 →
    deriv F (-6 * (deriv (fun s => deriv a s / a s) t + 2 * (deriv a t / a t) ^ 2)) ≠ 0 →
    (P Ω a F t₀ t ↔
      (deriv a t / a t) ^ 2 =
        (1 / 3) *
          ((3 * (deriv a t₀ / a t₀) ^ 2 * Ω * (a t₀ / a t) ^ 3) /
              deriv F (-6 * (deriv (fun s => deriv a s / a s) t + 2 * (deriv a t / a t) ^ 2))
            + (1 / deriv F (-6 * (deriv (fun s => deriv a s / a s) t
                  + 2 * (deriv a t / a t) ^ 2))) *
              ((1 / 2) *
                  (F (-6 * (deriv (fun s => deriv a s / a s) t + 2 * (deriv a t / a t) ^ 2))
                    - (-6 * (deriv (fun s => deriv a s / a s) t + 2 * (deriv a t / a t) ^ 2))
                      * deriv F (-6 * (deriv (fun s => deriv a s / a s) t
                          + 2 * (deriv a t / a t) ^ 2)))
                - 3 * (deriv a t / a t)
                  * deriv (fun s => -6 * (deriv (fun u => deriv a u / a u) s
                      + 2 * (deriv a s / a s) ^ 2)) t
                  * deriv (deriv F)
                      (-6 * (deriv (fun s => deriv a s / a s) t + 2 * (deriv a t / a t) ^ 2)))))

/-- **Item 3: the master equation for the Hubble parameter of section XI.**

Lines 143–157 (label `eq: presingleeq`):
`Ḣ = -(1/(2 F'(R))) [ 3 H_0² Ω_M^{(0)} a^{-3} + R̈ F''(R) + Ṙ (Ṙ F'''(R) - H F''(R)) ]`
(the printed `+ \ddot R F''(R) + + \dot R (...)` has a doubled `+` from a commented-out line break,
lines 151–154; read as a single `+`). `a^{-3}` is read as `(a(t₀)/a(t))³` for a non-normalised scale
factor, `H_0 = ȧ(t₀)/a(t₀)`, `H = ȧ/a`, `R = -6 (Ḣ + 2 H²)` (line 163).

Determination: the truth of `P Ω a F t₀ t` is fixed for every `Ω`, `a`, `F`, `t₀`, `t` with `a t ≠ 0`,
`a t₀ ≠ 0` and `F'(R(t)) ≠ 0`. Choice (source silent): no smoothness hypotheses; all derivatives are
Mathlib's `deriv` of explicit functions (`Ṙ = deriv R`, `R̈ = deriv (deriv R)`, `F'' = deriv (deriv F)`,
`F''' = deriv (deriv (deriv F))`). -/
structure FRMasterSpecJ (P : ℝ → (ℝ → ℝ) → (ℝ → ℝ) → ℝ → ℝ → Prop) : Prop where
  /-- The equation of lines 148–157 written out: with `H(s) = ȧ(s)/a(s)`,
  `R(s) = -6 (Ḣ(s) + 2 H(s)²)` (line 163),
  `Ḣ(t) = -(1/(2 F'(R(t)))) [ 3 H_0² Ω (a(t₀)/a(t))³ + R̈(t) F''(R(t))
  + Ṙ(t) (Ṙ(t) F'''(R(t)) - H(t) F''(R(t))) ]`.
  Side conditions: `a t ≠ 0`, `a t₀ ≠ 0`, `F'(R(t)) ≠ 0`. -/
  iff_master : ∀ (Ω : ℝ) (a F : ℝ → ℝ) (t₀ t : ℝ), a t ≠ 0 → a t₀ ≠ 0 →
    deriv F (-6 * (deriv (fun s => deriv a s / a s) t + 2 * (deriv a t / a t) ^ 2)) ≠ 0 →
    (P Ω a F t₀ t ↔
      deriv (fun s => deriv a s / a s) t =
        -(1 / (2 * deriv F (-6 * (deriv (fun s => deriv a s / a s) t
              + 2 * (deriv a t / a t) ^ 2)))) *
          (3 * (deriv a t₀ / a t₀) ^ 2 * Ω * (a t₀ / a t) ^ 3
            + deriv (deriv (fun s => -6 * (deriv (fun u => deriv a u / a u) s
                + 2 * (deriv a s / a s) ^ 2))) t
              * deriv (deriv F)
                  (-6 * (deriv (fun s => deriv a s / a s) t + 2 * (deriv a t / a t) ^ 2))
            + deriv (fun s => -6 * (deriv (fun u => deriv a u / a u) s
                + 2 * (deriv a s / a s) ^ 2)) t
              * (deriv (fun s => -6 * (deriv (fun u => deriv a u / a u) s
                    + 2 * (deriv a s / a s) ^ 2)) t
                  * deriv (deriv (deriv F))
                      (-6 * (deriv (fun s => deriv a s / a s) t + 2 * (deriv a t / a t) ^ 2))
                - (deriv a t / a t)
                  * deriv (deriv F)
                      (-6 * (deriv (fun s => deriv a s / a s) t
                        + 2 * (deriv a t / a t) ^ 2)))))

end Checked.Trust.SecondReadingSpecJ


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

/-!
# Sourced blind specification readings I, J and K against the three remaining pinned definitions
(run 2026-11-27T1028Z)

Same theorem names and shapes as `Checked/Trust/SpecAgreementGH.lean`: `meets_X_R : SpecR X` (the program's
definition is a model of reader R's specification) and `pins_X_R` (every function or condition meeting R's
specification equals / is equivalent to the program's, on R's domain). Readers I (Sonnet), J (Opus) and
K (Haiku) were handed a verbatim LaTeX excerpt of Bamba, Capozziello, Nojiri, Odintsov 2012 (the arXiv
e-print's §II, §VIII.C, §X and §XI up to its Ricci-scalar equation; `runs/2026-11-27T1028Z/sources/`) and, for each item,
only the quantity, its section and the Lean type; none saw the program's text.

Results: all nine readings AGREE.
* `rhoM` (dust density, §XI text after the curvature-fluid density): every reader generalised the source's
  `a⁻³` (written for a scale factor equal to one today) to the cube of the ratio of `a(t₀)` to `a(t)`, as the
  program does; determined where `a(t₀)`, `a(t)` are nonzero (I, K:
  positive; K also asks `a` differentiable at `t₀`).
* `FriedmannEq` (§XI expansion-rate equation) and `MasterEq` (§XI master equation): each reader wrote the equation in the source's
  divided form; the program's multiplied forms are equivalent wherever `F′(R) ≠ 0`, which every reader
  requires (K adds smoothness of `a` and `F`, the program's form holds without it).
* The convention question two readers raised (J: "§XI looks like a mix of conventions") is settled here
  in Lean: `friedmannEq_iff_standard`, `masterEq_iff_standard` prove that the program's §XI equations for
  `(a, F)` are exactly the common-sign metric F(R) equations (Ricci scalar `+6(Ḣ + 2H²)`, curvature-fluid
  term `R f′ − f` halved) for
  `f(x) = −F(−x)`, for every `a`, `F` and with no smoothness assumption: §XI is one consistent convention
  (the sign of `R` and of the Lagrangian flipped together), not a mix.
-/

namespace Checked.Trust.SpecAgreement

open Checked.Cosmography Checked.Cosmography.FRCosmo

/-! ## Algebra shared by every reader -/

private lemma alg_fr_half (h r f x y : ℝ) (hf : f ≠ 0) :
    3 * f * h ^ 2 = r + x / 2 - y ↔ h ^ 2 = 1 / 3 * (r / f + 1 / f * (x / 2 - y)) := by
  have e : 1 / 3 * (r / f + 1 / f * (x / 2 - y)) = (r + x / 2 - y) / (3 * f) := by
    field_simp; ring
  rw [e, eq_div_iff (mul_ne_zero (by norm_num) hf)]
  constructor <;> intro hh <;> linarith

private lemma alg_fr_mul (h r f x y : ℝ) (hf : f ≠ 0) :
    3 * f * h ^ 2 = r + x / 2 - y ↔ h ^ 2 = 1 / 3 * (r / f + 1 / f * (1 / 2 * x - y)) := by
  rw [alg_fr_half h r f x y hf]
  constructor <;> intro hh <;> rw [hh] <;> ring

private lemma alg_m (hd f z : ℝ) (hf : f ≠ 0) :
    -2 * f * hd = z ↔ hd = -(1 / (2 * f)) * z := by
  have e : -(1 / (2 * f)) * z = -z / (2 * f) := by field_simp
  rw [e, eq_div_iff (mul_ne_zero (by norm_num) hf)]
  constructor <;> intro hh <;> linarith

private lemma iter2 (F : ℝ → ℝ) : deriv^[2] F = deriv (deriv F) := rfl
private lemma iter3 (F : ℝ → ℝ) : deriv^[3] F = deriv (deriv (deriv F)) := rfl

/-- The program's dust density, written as every reader determines it. -/
private lemma rhoM_from (ρ : ℝ → (ℝ → ℝ) → ℝ → ℝ → ℝ) (Ω : ℝ) (a : ℝ → ℝ) (t₀ t : ℝ)
    (h0 : a t₀ ≠ 0) (h1 : a t ≠ 0)
    (hpres : ρ Ω a t₀ t₀ = 3 * (deriv a t₀ / a t₀) ^ 2 * Ω)
    (hsc : ρ Ω a t₀ t * a t ^ 3 = ρ Ω a t₀ t₀ * a t₀ ^ 3) :
    ρ Ω a t₀ t = rhoM Ω a t₀ t := by
  unfold rhoM hubble
  rw [hpres] at hsc
  have h3 : a t ^ 3 ≠ 0 := pow_ne_zero 3 h1
  rw [div_pow, ← eq_div_iff h3] at hsc
  rw [hsc]
  field_simp

private lemma rhoM_self (Ω : ℝ) (a : ℝ → ℝ) (t₀ : ℝ) (h0 : a t₀ ≠ 0) :
    rhoM Ω a t₀ t₀ = 3 * (deriv a t₀ / a t₀) ^ 2 * Ω := by
  unfold rhoM hubble
  rw [div_self h0]
  ring

private lemma rhoM_scale (Ω : ℝ) (a : ℝ → ℝ) (t₀ t : ℝ) (h0 : a t₀ ≠ 0) (h1 : a t ≠ 0) :
    rhoM Ω a t₀ t * a t ^ 3 = rhoM Ω a t₀ t₀ * a t₀ ^ 3 := by
  unfold rhoM
  rw [div_self h0]
  field_simp

/-! ## Reader I (Sonnet) -/

theorem meets_rhoM_I : SecondReadingSpecI.DustDensitySpecI rhoM :=
  ⟨fun Ω a t₀ h0 => rhoM_self Ω a t₀ h0.ne',
   fun Ω a t₀ t h0 h1 => rhoM_scale Ω a t₀ t h0.ne' h1.ne'⟩

theorem pins_rhoM_I (ρ : ℝ → (ℝ → ℝ) → ℝ → ℝ → ℝ) (h : SecondReadingSpecI.DustDensitySpecI ρ)
    (Ω : ℝ) (a : ℝ → ℝ) (t₀ t : ℝ) (h0 : 0 < a t₀) (h1 : 0 < a t) :
    ρ Ω a t₀ t = rhoM Ω a t₀ t :=
  rhoM_from ρ Ω a t₀ t h0.ne' h1.ne' (h.present Ω a t₀ h0) (h.scaling Ω a t₀ t h0 h1)

theorem meets_FriedmannEq_I : SecondReadingSpecI.FRFriedmannSpecI FriedmannEq :=
  ⟨fun Ω a F t₀ t _ _ hF => by
    unfold FriedmannEq
    rw [iter2]
    exact alg_fr_half _ _ _ _ _ hF⟩

theorem pins_FriedmannEq_I (P : ℝ → (ℝ → ℝ) → (ℝ → ℝ) → ℝ → ℝ → Prop)
    (h : SecondReadingSpecI.FRFriedmannSpecI P) (Ω : ℝ) (a F : ℝ → ℝ) (t₀ t : ℝ)
    (h0 : 0 < a t₀) (h1 : 0 < a t) (hF : deriv F (curv a t) ≠ 0) :
    P Ω a F t₀ t ↔ FriedmannEq Ω a F t₀ t :=
  (h.iff_eq Ω a F t₀ t h0 h1 hF).trans (meets_FriedmannEq_I.iff_eq Ω a F t₀ t h0 h1 hF).symm

theorem meets_MasterEq_I : SecondReadingSpecI.FRMasterSpecI MasterEq :=
  ⟨fun Ω a F t₀ t _ _ hF => by
    unfold MasterEq
    rw [iter2, iter2, iter3]
    exact alg_m _ _ _ hF⟩

theorem pins_MasterEq_I (P : ℝ → (ℝ → ℝ) → (ℝ → ℝ) → ℝ → ℝ → Prop)
    (h : SecondReadingSpecI.FRMasterSpecI P) (Ω : ℝ) (a F : ℝ → ℝ) (t₀ t : ℝ)
    (h0 : 0 < a t₀) (h1 : 0 < a t) (hF : deriv F (curv a t) ≠ 0) :
    P Ω a F t₀ t ↔ MasterEq Ω a F t₀ t :=
  (h.iff_eq Ω a F t₀ t h0 h1 hF).trans (meets_MasterEq_I.iff_eq Ω a F t₀ t h0 h1 hF).symm

/-! ## Reader J (Opus) -/

theorem meets_rhoM_J : SecondReadingSpecJ.DustDensitySpecJ rhoM :=
  ⟨fun Ω a t₀ h0 => rhoM_self Ω a t₀ h0,
   fun Ω a t₀ t h1 h0 => rhoM_scale Ω a t₀ t h0 h1⟩

theorem pins_rhoM_J (ρ : ℝ → (ℝ → ℝ) → ℝ → ℝ → ℝ) (h : SecondReadingSpecJ.DustDensitySpecJ ρ)
    (Ω : ℝ) (a : ℝ → ℝ) (t₀ t : ℝ) (h0 : a t₀ ≠ 0) (h1 : a t ≠ 0) :
    ρ Ω a t₀ t = rhoM Ω a t₀ t :=
  rhoM_from ρ Ω a t₀ t h0 h1 (h.present_value Ω a t₀ h0) (h.dust_scaling Ω a t₀ t h1 h0)

theorem meets_FriedmannEq_J : SecondReadingSpecJ.FRFriedmannSpecJ FriedmannEq :=
  ⟨fun Ω a F t₀ t _ _ hF => by
    unfold FriedmannEq
    rw [iter2]
    exact alg_fr_mul _ _ _ _ _ hF⟩

theorem pins_FriedmannEq_J (P : ℝ → (ℝ → ℝ) → (ℝ → ℝ) → ℝ → ℝ → Prop)
    (h : SecondReadingSpecJ.FRFriedmannSpecJ P) (Ω : ℝ) (a F : ℝ → ℝ) (t₀ t : ℝ)
    (h1 : a t ≠ 0) (h0 : a t₀ ≠ 0) (hF : deriv F (curv a t) ≠ 0) :
    P Ω a F t₀ t ↔ FriedmannEq Ω a F t₀ t :=
  (h.iff_friedmann Ω a F t₀ t h1 h0 hF).trans
    (meets_FriedmannEq_J.iff_friedmann Ω a F t₀ t h1 h0 hF).symm

theorem meets_MasterEq_J : SecondReadingSpecJ.FRMasterSpecJ MasterEq :=
  ⟨fun Ω a F t₀ t _ _ hF => by
    unfold MasterEq
    rw [iter2, iter2, iter3]
    exact alg_m _ _ _ hF⟩

theorem pins_MasterEq_J (P : ℝ → (ℝ → ℝ) → (ℝ → ℝ) → ℝ → ℝ → Prop)
    (h : SecondReadingSpecJ.FRMasterSpecJ P) (Ω : ℝ) (a F : ℝ → ℝ) (t₀ t : ℝ)
    (h1 : a t ≠ 0) (h0 : a t₀ ≠ 0) (hF : deriv F (curv a t) ≠ 0) :
    P Ω a F t₀ t ↔ MasterEq Ω a F t₀ t :=
  (h.iff_master Ω a F t₀ t h1 h0 hF).trans (meets_MasterEq_J.iff_master Ω a F t₀ t h1 h0 hF).symm

/-! ## Reader K (Haiku) -/

theorem meets_rhoM_K : SecondReadingSpecK.DustDensitySpecK rhoM :=
  ⟨fun Ω a t₀ t h0 h1 => by
    have := rhoM_scale Ω a t₀ t h0.ne' h1.ne'
    have h3 : a t ^ 3 ≠ 0 := pow_ne_zero 3 h1.ne'
    rw [div_pow, mul_div_assoc', eq_div_iff h3]
    exact this,
   fun Ω a t₀ h0 _ => rhoM_self Ω a t₀ h0.ne'⟩

theorem pins_rhoM_K (ρ : ℝ → (ℝ → ℝ) → ℝ → ℝ → ℝ) (h : SecondReadingSpecK.DustDensitySpecK ρ)
    (Ω : ℝ) (a : ℝ → ℝ) (t₀ t : ℝ) (h0 : 0 < a t₀) (h1 : 0 < a t) (hd : DifferentiableAt ℝ a t₀) :
    ρ Ω a t₀ t = rhoM Ω a t₀ t := by
  apply rhoM_from ρ Ω a t₀ t h0.ne' h1.ne' (h.present Ω a t₀ h0 hd)
  rw [h.scaling Ω a t₀ t h0 h1, div_pow]
  field_simp

theorem meets_FriedmannEq_K : SecondReadingSpecK.FRFriedmannSpecK FriedmannEq :=
  ⟨fun Ω a F t₀ t _ _ _ _ hF => by
    unfold FriedmannEq
    rw [iter2]
    exact alg_fr_mul _ _ _ _ _ hF⟩

theorem pins_FriedmannEq_K (P : ℝ → (ℝ → ℝ) → (ℝ → ℝ) → ℝ → ℝ → Prop)
    (h : SecondReadingSpecK.FRFriedmannSpecK P) (Ω : ℝ) (a F : ℝ → ℝ) (t₀ t : ℝ)
    (h0 : 0 < a t₀) (hd : DifferentiableAt ℝ a t₀)
    (hn : ∀ᶠ s in nhds t, 0 < a s ∧ ContDiffAt ℝ 3 a s) (hFs : ContDiffAt ℝ 2 F (curv a t))
    (hF : deriv F (curv a t) ≠ 0) :
    P Ω a F t₀ t ↔ FriedmannEq Ω a F t₀ t :=
  (h.iff Ω a F t₀ t h0 hd hn hFs hF).trans (meets_FriedmannEq_K.iff Ω a F t₀ t h0 hd hn hFs hF).symm

theorem meets_MasterEq_K : SecondReadingSpecK.FRMasterSpecK MasterEq :=
  ⟨fun Ω a F t₀ t _ _ _ _ hF => by
    unfold MasterEq
    rw [iter2, iter2, iter3]
    exact alg_m _ _ _ hF⟩

theorem pins_MasterEq_K (P : ℝ → (ℝ → ℝ) → (ℝ → ℝ) → ℝ → ℝ → Prop)
    (h : SecondReadingSpecK.FRMasterSpecK P) (Ω : ℝ) (a F : ℝ → ℝ) (t₀ t : ℝ)
    (h0 : 0 < a t₀) (hd : DifferentiableAt ℝ a t₀)
    (hn : ∀ᶠ s in nhds t, 0 < a s ∧ ContDiffAt ℝ 4 a s)
    (hFs : ∀ᶠ y in nhds (curv a t), ContDiffAt ℝ 3 F y) (hF : deriv F (curv a t) ≠ 0) :
    P Ω a F t₀ t ↔ MasterEq Ω a F t₀ t :=
  (h.iff Ω a F t₀ t h0 hd hn hFs hF).trans (meets_MasterEq_K.iff Ω a F t₀ t h0 hd hn hFs hF).symm

/-! ## §XI is one convention: the common-sign F(R) equations for `f(x) = −F(−x)`

Readers I, J, K all flagged that §XI's `R = −6(Ḣ + 2H²)` is minus the usual Ricci scalar of the stated metric
(the source's §VIII.C has `+6`), and J asked whether its expansion-rate and master equations mix conventions. The two theorems below
answer it for every scale factor and every `F`, with no smoothness assumption (Mathlib's `deriv` of a
composition with negation needs none): the program's §XI equations for `(a, F)` are the textbook metric F(R)
equations, with Ricci scalar `+6(Ḣ + 2H²)` and curvature fluid `(R f′ − f)/2 − 3HṘf″`, for the Lagrangian
`f(x) = −F(−x)`. Flipping the sign of `R` and of the Lagrangian together is a convention, not an error; with
`F(R) = R` both describe general relativity. -/

private lemma deriv_negneg (G : ℝ → ℝ) : deriv (fun x => -G (-x)) = fun y => deriv G (-y) := by
  funext y
  have e : (fun x => -G (-x)) = -(fun x => G (-x)) := rfl
  rw [e, deriv.neg, deriv_comp_neg, neg_neg]

private lemma deriv_neg_arg (G : ℝ → ℝ) : deriv (fun x => G (-x)) = fun y => -deriv G (-y) := by
  funext y
  exact deriv_comp_neg G y

private lemma curv_std (a : ℝ → ℝ) :
    (fun s => 6 * (deriv (hubble a) s + 2 * hubble a s ^ 2)) = -curv a := by
  funext s
  simp only [Pi.neg_apply, curv]
  ring

/-- The program's §XI expansion-rate equation for `(a, F)` is the common-sign one for `f(x) = −F(−x)`:
`3 f′(Rₛ) H² = ρ_M + (Rₛ f′(Rₛ) − f(Rₛ))/2 − 3 H Ṙₛ f″(Rₛ)` with `Rₛ = 6(Ḣ + 2H²)`. -/
theorem friedmannEq_iff_standard (Ω : ℝ) (a F : ℝ → ℝ) (t₀ t : ℝ) :
    FriedmannEq Ω a F t₀ t ↔
      3 * deriv (fun x => -F (-x)) (6 * (deriv (hubble a) t + 2 * hubble a t ^ 2)) * hubble a t ^ 2 =
        rhoM Ω a t₀ t
          + ((6 * (deriv (hubble a) t + 2 * hubble a t ^ 2))
                * deriv (fun x => -F (-x)) (6 * (deriv (hubble a) t + 2 * hubble a t ^ 2))
              - (fun x => -F (-x)) (6 * (deriv (hubble a) t + 2 * hubble a t ^ 2))) / 2
          - 3 * hubble a t * deriv (fun s => 6 * (deriv (hubble a) s + 2 * hubble a s ^ 2)) t
              * deriv^[2] (fun x => -F (-x)) (6 * (deriv (hubble a) t + 2 * hubble a t ^ 2)) := by
  have hR : 6 * (deriv (hubble a) t + 2 * hubble a t ^ 2) = -curv a t := by unfold curv; ring
  rw [curv_std, iter2, deriv_negneg, deriv_neg_arg, hR, deriv.neg]
  simp only [neg_neg]
  unfold FriedmannEq
  rw [iter2]
  constructor <;> intro h <;> linarith

/-- The program's §XI master equation for `(a, F)` is the common-sign one for `f(x) = −F(−x)`:
`−2 f′(Rₛ) Ḣ = ρ_M + R̈ₛ f″(Rₛ) + Ṙₛ (Ṙₛ f‴(Rₛ) − H f″(Rₛ))` with `Rₛ = 6(Ḣ + 2H²)`. -/
theorem masterEq_iff_standard (Ω : ℝ) (a F : ℝ → ℝ) (t₀ t : ℝ) :
    MasterEq Ω a F t₀ t ↔
      -2 * deriv (fun x => -F (-x)) (6 * (deriv (hubble a) t + 2 * hubble a t ^ 2))
          * deriv (hubble a) t =
        rhoM Ω a t₀ t
          + deriv^[2] (fun s => 6 * (deriv (hubble a) s + 2 * hubble a s ^ 2)) t
              * deriv^[2] (fun x => -F (-x)) (6 * (deriv (hubble a) t + 2 * hubble a t ^ 2))
          + deriv (fun s => 6 * (deriv (hubble a) s + 2 * hubble a s ^ 2)) t
              * (deriv (fun s => 6 * (deriv (hubble a) s + 2 * hubble a s ^ 2)) t
                  * deriv^[3] (fun x => -F (-x)) (6 * (deriv (hubble a) t + 2 * hubble a t ^ 2))
                - hubble a t
                  * deriv^[2] (fun x => -F (-x)) (6 * (deriv (hubble a) t + 2 * hubble a t ^ 2))) := by
  have hR : 6 * (deriv (hubble a) t + 2 * hubble a t ^ 2) = -curv a t := by unfold curv; ring
  rw [curv_std, iter2, iter2, iter3, deriv_negneg, deriv_neg_arg, deriv_negneg, hR, deriv.neg',
    show deriv (fun x => -deriv (curv a) x) t = -deriv (deriv (curv a)) t from deriv.neg]
  simp only [neg_neg]
  unfold MasterEq
  rw [iter2, iter2, iter3]
  constructor <;> intro h <;> linarith

end Checked.Trust.SpecAgreement
