import Mathlib.Analysis.Calculus.Deriv.Basic

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
