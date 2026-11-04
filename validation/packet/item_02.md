# Item 02

**Area:** F7

**Source:** Bamba, Capozziello, Nojiri, Odintsov, Astrophys. Space Sci. 342, 155 (2012), arXiv:1205.3421, Eqs. (10.61)–(10.63), verbatim from Capozziello & Salzano 2009 Eqs. (62)–(64): curvature terms of the y-redshift angular-diameter-distance coefficients D³_{A,y}, D⁴_{A,y} wrong

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**It holds that**

- it is false that (`BambaDA4ClaimPast`)

Program definitions in this claim:

- `BambaDA4ClaimPast` — CLAIM, not pinned: means for every `K : ℝ`, for every `a : ℝ → ℝ`, for every `t₀ : ℝ`, if `ContDiff ℝ ⊤ a`, then if for every `t : ℝ`, `0 < a t`, then if `0 < hubble a t₀`, then `(fun t => remA correctDA3 printedDA4 K a t₀ t) =o[nhdsWithin t₀ (Set.Iio t₀)] fun t => yred a t₀ t ^ 5`
- `DA1 q` — PRINTED, not pinned (for `q : ℝ`): is defined as `-(1 / 2) * (1 + q)`
- `DA2 q j Ω` — PRINTED, not pinned (for `q : ℝ`, `j : ℝ`, `Ω : ℝ`): is defined as `-(1 / 6) * (-q - 3 * q ^ 2 + j + Ω)`
- `angDist K a t₀ t` — **PINNED** (pin theorem `angDistSpec_pins`): the angular-diameter distance d_L/(1 + z)², at observation time `t₀`, of a source emitting at time `t`, in the FLRW model with scale factor `a` and curvature constant `K` (c = 1)
- `correctDA3 q j s Ω` — FORMULA, not pinned (for `q : ℝ`, `j : ℝ`, `s : ℝ`, `Ω : ℝ`): is defined as `printedDA3 q j s Ω + q * (Ω - 1) / 4`
- `cosmoCoeff n a t` — **PINNED** (pin theorem `cosmoCoeffCore_pins`): the `n`-th cosmographic coefficient a⁽ⁿ⁾(t)/(a(t)·H(t)ⁿ) of the scale factor `a` at time `t` (n = `n`; j, s, l, m for n = 3, 4, 5, 6; the deceleration parameter is minus the n = 2 coefficient)
- `decel a t` — **PINNED** (pin theorem `decelSpec_pins`): the deceleration parameter −a″(t)·a(t)/a′(t)² of the scale factor `a` at time `t`
- `hubble a t` — **PINNED** (pin theorem `hubbleSpec_pins`): the Hubble rate a′(t)/a(t) of the scale factor `a` at time `t`
- `omega0 K a t₀` — **PINNED** (pin theorem `omega0Spec_pins`): the total density parameter Ω₀ = 1 + K/(H₀²·a₀²) at time `t₀` for curvature constant `K` and scale factor `a` (c = 1; H₀, a₀ the Hubble rate and scale factor at `t₀`; Ω_k = 1 − Ω₀)
- `printedDA3 q j s Ω` — PRINTED, not pinned (for `q : ℝ`, `j : ℝ`, `s : ℝ`, `Ω : ℝ`): is defined as `-(1 / 24) * (-2 * q + 3 * q ^ 2 + 15 * q ^ 3 - j - 10 * q * j - s + 2 * Ω)`
- `printedDA4 q j s l Ω` — PRINTED, not pinned (for `q : ℝ`, `j : ℝ`, `s : ℝ`, `l : ℝ`, `Ω : ℝ`): is defined as `-(1 / 120) * (1 - 6 * q + 9 * q ^ 2 - 15 * q ^ 3 - 105 * q ^ 4 + 10 * q * j + 105 * q ^ 2 * j + 15 * q * s + -3 * j - 10 * j ^ 2 + s + l + 5 * Ω)`
- `remA D3 D4 K a t₀ t` — COMPOSITE, not pinned (for `D3 : ℝ → ℝ → ℝ → ℝ → ℝ`, `D4 : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ`, `K : ℝ`, `a : ℝ → ℝ`, `t₀ : ℝ`, `t : ℝ`): is defined as `hubble a t₀ * angDist K a t₀ t - yred a t₀ t * (1 + DA1 (decel a t₀) * yred a t₀ t + DA2 (decel a t₀) (cosmoCoeff 3 a t₀) (omega0 K a t₀) * yred a t₀ t ^ 2 + D3 (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) (omega0 K a t₀) * yred a t₀ t ^ 3 + D4 (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) (cosmoCoeff 5 a t₀) (omega0 K a t₀) * yred a t₀ t ^ 4)`
- `yred a t₀ t` — **PINNED** (pin theorem `yRedSpec_pins`): the y-redshift z/(1 + z), observed at time `t₀`, of light emitted at time `t` (scale factor `a`)

## Author's paraphrase (hand-written; checked only by prose rules)

The review's claim (10.62)–(10.63) is false even for past emission only (`t → t₀⁻`): see
`bambaDA4Claim_false`.

## Formal statement (Lean 4)

```lean
theorem bambaDA4ClaimPast_false : ¬ BambaDA4ClaimPast := …
```

## Definitions it uses

See GLOSSARY.md: `Cosmography.Aviles.cosmoCoeff`, `Cosmography.BambaA.angDist`, `Cosmography.BambaK.omega0`, `Cosmography.BambaY.yred`, `Cosmography.decel`, `Cosmography.hubble`, `Cosmography.BambaA.BambaDA4ClaimPast`, `Cosmography.BambaA.DA1`, `Cosmography.BambaA.DA2`, `Cosmography.BambaA.printedDA3`, `Cosmography.BambaA.printedDA4`, `Chemistry.RKReduced.q`, `Cosmography.BambaA.correctDA3`, `Cosmography.BambaA.remA`, `Cosmography.BambaK.lumDist`, `Cosmography.BambaY.comoving`, `Cosmography.CCS.D3`, `Cosmography.Transverse.transverse`, `Cosmography.redshift`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: cosmoCoeff, angDist, omega0, yred, decel, hubble.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): BambaDA4ClaimPast, DA1², DA2², printedDA3², printedDA4².
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): unconditional.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): cosmoCoeff: n = 3, n = 4, n = 5.
- Source file: `Checked/Cosmography/BambaAngular.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 02
