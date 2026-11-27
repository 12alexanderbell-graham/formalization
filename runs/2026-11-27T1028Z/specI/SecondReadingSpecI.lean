import Mathlib.Analysis.Calculus.Deriv.Basic

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
