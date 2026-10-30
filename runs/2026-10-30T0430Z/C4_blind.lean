import Mathlib

/-!
# C4 (blind restatement): Capozziello–Lazkoz–Salzano, PRD 84 124061 (2011), Eq. (22)

Modelling choices (written from `source_C4.md` alone):

* Time and scale factor: `a : ℝ → ℝ`, `t0 : ℝ` is "today".  Everything in Eq. (2) is a
  pointwise derivative at `t0`, so the model is only imposed on an open interval
  `(t0 - ε, t0 + ε)`; outside it `a` is unconstrained.
* Smoothness: `a` is `C^5` on that interval (Eq. (2) needs up to `d⁵a/dt⁵`).  Since the
  interval is open, Mathlib's global `iteratedDeriv 5 a t0` is the genuine fifth derivative.
  (The ODE `ȧ = a H₀ E` actually forces `a` analytic there; we do not assume more than C^5.)
* Positivity / sign: `a > 0` on the interval (so `z = a(t0)/a(t) - 1` and `(1+z)^p` make sense),
  and `H₀ = ȧ(t0)/a(t0) > 0` (expanding universe).  Eq. (17) only fixes `H²`, so the sign of
  `H₀` is an extra (physically obvious) choice; with `H₀ > 0` and continuity of `H`,
  `H > 0` throughout the interval, and the ODE `ȧ = a H₀ E(z)` determines `a` up to
  normalisation, so `l0` is well defined.
* Eq. (17) is stated as `H(t)² = H₀² · E²(z(t))` with `H₀ := H(t0)` (not a separate
  parameter), `ΩX = 1 - Ωm` (flatness), and the real power `(1+z)^{3(1+w0+wa)}` taken as
  `Real.rpow` (base `1+z = a(t0)/a(t) > 0`).  Normalisation of `a(t0)` is left free: every
  quantity in Eq. (2) and `z` is scale-invariant.  No relation `a(t0) = 1` is imposed, although
  Eq. (16)'s `w = w0 + wa(1-a)` silently uses it; we use the `z`-form of `w`, which is what (17) uses.
* Parameters: `Ωm, w0, wa` range over all of `ℝ`.  The source intends `0 < Ωm < 1`, but Eq. (22)
  is a polynomial identity, and `E²(0) = 1` so the model is non-degenerate near `t0` for any
  real parameters; restricting to `0 < Ωm < 1` would give a weaker (implied) claim.
* `l` coefficient: `l(t) = a⁽⁵⁾(t) / a(t) / H(t)⁵`, read off Eq. (2) with no sign
  (unlike `q`, which carries a minus sign).  Ambiguity: none in the printed algebra beyond
  the reading of `(1 − Ωm)/4 [213 + (7 − Ωm) wa] wa` as `((1-Ωm)/4) * (213 + (7-Ωm) wa) * wa`.
-/

namespace C4Blind

noncomputable section

/-- Hubble rate, Eq. (2): `H = ȧ / a`. -/
def hubble (a : ℝ → ℝ) (t : ℝ) : ℝ := deriv a t / a t

/-- Redshift, `z := a(t₀)/a(t) − 1`. -/
def redshift (a : ℝ → ℝ) (t0 t : ℝ) : ℝ := a t0 / a t - 1

/-- `E²(z)` of Eq. (17), flat, `ΩX = 1 − Ωm`. -/
def E2CPL (Ωm w0 wa z : ℝ) : ℝ :=
  Ωm * (1 + z) ^ (3 : ℕ)
    + (1 - Ωm) * (1 + z) ^ (3 * (1 + w0 + wa)) * Real.exp (-3 * wa * z / (1 + z))

/-- Fifth cosmographic coefficient, Eq. (2): `l = (1/a) a⁽⁵⁾ / H⁵`. -/
def lCoeff (a : ℝ → ℝ) (t : ℝ) : ℝ :=
  iteratedDeriv 5 a t / a t / hubble a t ^ 5

/-- The model hypothesis: `a` is a positive `C^5` scale factor near `t0`, expanding at `t0`,
whose Hubble rate obeys Eq. (17) on a neighbourhood of `t0`. -/
def CPLModel (Ωm w0 wa t0 : ℝ) (a : ℝ → ℝ) : Prop :=
  ∃ ε > 0,
    ContDiffOn ℝ 5 a (Set.Ioo (t0 - ε) (t0 + ε)) ∧
    (∀ t ∈ Set.Ioo (t0 - ε) (t0 + ε), 0 < a t) ∧
    0 < hubble a t0 ∧
    ∀ t ∈ Set.Ioo (t0 - ε) (t0 + ε),
      hubble a t ^ 2 = hubble a t0 ^ 2 * E2CPL Ωm w0 wa (redshift a t0 t)

/-- The right-hand side of Eq. (22), transcribed literally. -/
def printedL0 (Ωm w0 wa : ℝ) : ℝ :=
  35 / 2
    + (1 - Ωm) / 4 * (213 + (7 - Ωm) * wa) * wa
    + (1 - Ωm) / 4 * (489 + 9 * (82 - 21 * Ωm) * wa) * w0
    + 9 / 2 * (1 - Ωm) * (67 - 21 * Ωm + 3 / 2 * (23 - 11 * Ωm) * wa) * w0 ^ 2
    + 27 / 4 * (1 - Ωm) * (47 - 24 * Ωm) * w0 ^ 3
    + 81 / 2 * (1 - Ωm) * (3 - 2 * Ωm) * w0 ^ 4

/-- Eq. (22) as printed: for all parameters and every scale factor obeying the model,
`l0 = printedL0`. -/
def BlindL0Claim : Prop :=
  ∀ (Ωm w0 wa t0 : ℝ) (a : ℝ → ℝ),
    CPLModel Ωm w0 wa t0 a → lCoeff a t0 = printedL0 Ωm w0 wa

end

end C4Blind
