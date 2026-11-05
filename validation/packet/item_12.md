# Item 12

**Area:** F3

**Source:** Capozziello, Cardone, Salzano, PRD 78, 063504 (2008), arXiv:0802.1583v2, App. A, Eq. (A2): lookback-distance z⁵ coefficient, 7/2 q₀⁴ should be 7/8 q₀⁴

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**For every** `a : ℝ → ℝ`, `t₀ : ℝ`:

**assuming**

1. `ContDiffAt ℝ 5 a t₀`
2. `a t₀ ≠ 0`
3. `hubble a t₀ ≠ 0`

**then**

- `(fun t => remainder correctD4 a t₀ t) =o[nhds t₀] fun t => redshift a t₀ t ^ 5`

Program definitions in this claim:

- `D1 q` — PRINTED, not pinned, so only the formula shown is checked, not its name (for `q : ℝ`): is defined as `-(1 + q / 2)`
- `D2 q j` — PRINTED, not pinned, so only the formula shown is checked, not its name (for `q : ℝ`, `j : ℝ`): is defined as `1 + q + q ^ 2 / 2 - j / 6`
- `D3 q j s` — PRINTED, not pinned, so only the formula shown is checked, not its name (for `q : ℝ`, `j : ℝ`, `s : ℝ`): is defined as `-(1 + 3 / 2 * q + 3 / 2 * q ^ 2 + 5 / 8 * q ^ 3 - 1 / 2 * j - 5 / 12 * q * j - s / 24)`
- `correctD4 q j s l` — FORMULA, not pinned, so only the formula shown is checked, not its name (for `q : ℝ`, `j : ℝ`, `s : ℝ`, `l : ℝ`): is defined as `1 + 2 * q + 3 * q ^ 2 + 5 / 2 * q ^ 3 + 7 / 8 * q ^ 4 - 5 / 3 * q * j - 7 / 8 * q ^ 2 * j - j + j ^ 2 / 12 - 1 / 8 * q * s - s / 6 - l / 120`
- `cosmoCoeff n a t` — **PINNED** (pin theorem `cosmoCoeffCore_pins`): the `n`-th cosmographic coefficient a⁽ⁿ⁾(t)/(a(t)·H(t)ⁿ) of the scale factor `a` at time `t` (n = `n`; j, s, l, m for n = 3, 4, 5, 6; the deceleration parameter is minus the n = 2 coefficient)
- `decel a t` — **PINNED** (pin theorem `decelSpec_pins`): the deceleration parameter −a″(t)·a(t)/a′(t)² of the scale factor `a` at time `t`
- `hubble a t` — **PINNED** (pin theorem `hubbleSpec_pins`): the Hubble rate a′(t)/a(t) of the scale factor `a` at time `t`
- `redshift a t₀ t` — **PINNED** (pin theorem `redshiftCore_pins`): the redshift a(`t₀`)/a(`t`) − 1, observed at time `t₀`, of light emitted at time `t` (scale factor `a`)
- `remainder D4 a t₀ t` — COMPOSITE, not pinned, so only the formula shown is checked, not its name (for `D4 : ℝ → ℝ → ℝ → ℝ → ℝ`, `a : ℝ → ℝ`, `t₀ : ℝ`, `t : ℝ`): is defined as `hubble a t₀ * (t₀ - t) - series (D4 (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) (cosmoCoeff 5 a t₀)) (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) (redshift a t₀ t)`
- `series d4 q j s z` — FORMULA, not pinned, so only the formula shown is checked, not its name (for `d4 : ℝ`, `q : ℝ`, `j : ℝ`, `s : ℝ`, `z : ℝ`): is defined as `z * (1 + D1 q * z + D2 q j * z ^ 2 + D3 q j s * z ^ 3 + d4 * z ^ 4)`

## Author's paraphrase (hand-written; checked only by prose rules)

**Lookback time to fifth order in redshift** (correct version of Eq. (A2)): for every
scale factor that is `C⁵` at `t₀`, with `a(t₀) ≠ 0` and `H₀ ≠ 0`.

## Formal statement (Lean 4)

```lean
theorem lookback_fifth_order (a : ℝ → ℝ) (t₀ : ℝ) (ha : ContDiffAt ℝ 5 a t₀)
    (ha0 : a t₀ ≠ 0) (hH : hubble a t₀ ≠ 0) :
    (fun t => remainder correctD4 a t₀ t) =o[𝓝 t₀] (fun t => redshift a t₀ t ^ 5) := …
```

## Definitions it uses

See GLOSSARY.md: `Cosmography.Aviles.cosmoCoeff`, `Cosmography.decel`, `Cosmography.hubble`, `Cosmography.redshift`, `Cosmography.CCS.D1`, `Cosmography.CCS.D2`, `Cosmography.CCS.D3`, `Cosmography.CCS.correctD4`, `Cosmography.CCS.remainder`, `Cosmography.CCS.series`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: cosmoCoeff, decel, hubble, redshift.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): D1², D2², D3².
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): `lookback_fifth_order`.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): cosmoCoeff: n = 3, n = 4, n = 5.
- Source file: `Checked/Cosmography/CCSLookback.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 12
