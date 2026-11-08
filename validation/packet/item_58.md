# Item 58

**Area:** F11

**Source:** Demianski, Piedipalumbo, Sawant, Amati, A&A 598, A113 (2017), arXiv:1609.09631 (v1, v2), p. 3: flat z-series D⁴_L has −105q₀⁴ (should be +105q₀⁴) and D⁴_A (Eq. (23)) has +137j₀ (should be −137j₀); the D⁴_L error is reprinted in Lusso et al., A&A 628, L4 (2019), arXiv:1907.07692 (v1–v4), the quasar+SN+GRB paper claiming > 4σ tension with flat ΛCDM

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**For every** `a : ℝ → ℝ`, `t₀ : ℝ`:

**assuming**

1. `ContDiffAt ℝ 5 a t₀`
2. `a t₀ ≠ 0`
3. `hubble a t₀ ≠ 0`
4. `cosmoCoeff 3 a t₀ ≠ 0`

**then**

- it is false that (`(fun t => remAz (fun q j s l x => demDA4 q j s l) 0 a t₀ t) =o[nhdsWithin t₀ (Set.Iio t₀)] fun t => redshift a t₀ t ^ 5`)

Program definitions in this claim:

- `DA1z q` — PRINTED, not pinned; an independent blind second reading of the source agrees with this transcription (`Checked.Trust.Transcriptions.agree_DA1z`); its name is not checked (for `q : ℝ`): is defined as `-(1 / 2) * (3 + q)`
- `DA2z q j k` — PRINTED, not pinned; an independent blind second reading of the source agrees with this transcription (`Checked.Trust.Transcriptions.agree_DA2z`); its name is not checked (for `q : ℝ`, `j : ℝ`, `k : ℝ`): is defined as `1 / 6 * (11 + 7 * q + 3 * q ^ 2 - j - k)`
- `DA3z q j s k` — PRINTED, not pinned; an independent blind second reading of the source agrees with this transcription (`Checked.Trust.Transcriptions.agree_DA3z`); its name is not checked (for `q : ℝ`, `j : ℝ`, `s : ℝ`, `k : ℝ`): is defined as `-(1 / 24) * (50 + 46 * q + 39 * q ^ 2 + 15 * q ^ 3 - 13 * j - 10 * q * j - s - 2 * k * (5 + 3 * q))`
- `angDist K a t₀ t` — **PINNED** (pin theorem `angDistSpec_pins`): the angular-diameter distance d_L/(1 + z)², at observation time `t₀`, of a source emitting at time `t`, in the FLRW model with scale factor `a` and curvature constant `K` (c = 1)
- `cosmoCoeff n a t` — **PINNED** (pin theorem `cosmoCoeffCore_pins`): the `n`-th cosmographic coefficient a⁽ⁿ⁾(t)/(a(t)·H(t)ⁿ) of the scale factor `a` at time `t` (n = `n`; j, s, l, m for n = 3, 4, 5, 6; the deceleration parameter is minus the n = 2 coefficient)
- `curvK K a t₀` — **PINNED** (pin theorem `curvKSpec_pins`): the curvature parameter K/(H₀²·a₀²) at time `t₀` for curvature constant `K` and scale factor `a` (c = 1; equal to −Ω_k)
- `decel a t` — **PINNED** (pin theorem `decelSpec_pins`): the deceleration parameter −a″(t)·a(t)/a′(t)² of the scale factor `a` at time `t`
- `demDA4 q j s l` — PRINTED, not pinned; an independent blind second reading of the source agrees with this transcription (`Checked.Trust.Transcriptions.agree_demDA4`); its name is not checked (for `q : ℝ`, `j : ℝ`, `s : ℝ`, `l : ℝ`): is defined as `1 / 120 * (274 + 326 * q + 411 * q ^ 2 + 315 * q ^ 3 + 105 * q ^ 4 - 210 * q * j - 105 * q ^ 2 * j - 15 * q * s + 137 * j + 10 * j ^ 2 - 21 * s - l)`
- `hubble a t` — **PINNED** (pin theorem `hubbleSpec_pins`): the Hubble rate a′(t)/a(t) of the scale factor `a` at time `t`
- `redshift a t₀ t` — **PINNED** (pin theorem `redshiftCore_pins`): the redshift a(`t₀`)/a(`t`) − 1, observed at time `t₀`, of light emitted at time `t` (scale factor `a`)
- `remAz D4 K a t₀ t` — COMPOSITE, not pinned, so only the formula shown is checked, not its name (for `D4 : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ`, `K : ℝ`, `a : ℝ → ℝ`, `t₀ : ℝ`, `t : ℝ`): is defined as `hubble a t₀ * angDist K a t₀ t - seriesZ (DA1z (decel a t₀)) (DA2z (decel a t₀) (cosmoCoeff 3 a t₀) (curvK K a t₀)) (DA3z (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) (curvK K a t₀)) (D4 (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) (cosmoCoeff 5 a t₀) (curvK K a t₀)) (redshift a t₀ t)`
- `seriesZ d1 d2 d3 d4 z` — FORMULA, not pinned; name and body agree with a blind second formulation (`Checked.Trust.Formulations.agree_seriesZ`) (for `d1 : ℝ`, `d2 : ℝ`, `d3 : ℝ`, `d4 : ℝ`, `z : ℝ`): is defined as `z * (1 + d1 * z + d2 * z ^ 2 + d3 * z ^ 3 + d4 * z ^ 4)`

## Author's paraphrase (hand-written; checked only by prose rules)

The printed `D⁴_A` fails, from the past, in every flat `C⁵` model with `a(t₀) ≠ 0`, `H₀ ≠ 0`,
`j₀ ≠ 0`.

## Formal statement (Lean 4)

```lean
theorem demDA4_fails_past (a : ℝ → ℝ) (t₀ : ℝ) (ha : ContDiffAt ℝ 5 a t₀) (ha0 : a t₀ ≠ 0)
    (hH : hubble a t₀ ≠ 0) (hj : cosmoCoeff 3 a t₀ ≠ 0) :
    ¬ (fun t => remAz (fun q j s l _ => demDA4 q j s l) 0 a t₀ t)
      =o[𝓝[<] t₀] (fun t => redshift a t₀ t ^ 5) := …
```

## Definitions it uses

See GLOSSARY.md: `Cosmography.Aviles.cosmoCoeff`, `Cosmography.BambaA.angDist`, `Cosmography.BambaZ.curvK`, `Cosmography.decel`, `Cosmography.hubble`, `Cosmography.redshift`, `Cosmography.BambaZ.DA1z`, `Cosmography.BambaZ.DA2z`, `Cosmography.BambaZ.DA3z`, `Cosmography.DemianskiZ.demDA4`, `Cosmography.BambaK.lumDist`, `Cosmography.BambaY.comoving`, `Cosmography.BambaZ.remAz`, `Cosmography.BambaZ.seriesZ`, `Cosmography.Transverse.transverse`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: cosmoCoeff, angDist, curvK, decel, hubble, redshift.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): DA1z², DA2z², DA3z², demDA4².
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): `demDA4_fails_past`.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): cosmoCoeff: n = 3, n = 4, n = 5; remAz: K = 0; angDist: K = 0; curvK: K = 0.
- Source file: `Checked/Cosmography/DemianskiZ.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 58
