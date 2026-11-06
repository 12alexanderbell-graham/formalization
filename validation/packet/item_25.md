# Item 25

**Area:** F8

**Source:** Bamba, Capozziello, Nojiri, Odintsov, Astrophys. Space Sci. 342, 155 (2012), arXiv:1205.3421, Eqs. (10.38)–(10.51), verbatim from Capozziello & Salzano 2009 (arXiv:0902.0088) Eqs. (31)–(52): z-redshift d_L and d_A fourth-order coefficients D⁴_L, D⁴_A miss the curvature-squared term

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**It holds that**

- it is false that (`(fun t => remLz printedDL4z (-1) (fun t => t) 1 t) =o[nhdsWithin 1 (Set.Iio 1)] fun t => redshift (fun t => t) 1 t ^ 5`)

Program definitions in this claim:

- `DL1z q` — PRINTED, not pinned; an independent blind second reading of the source agrees with this transcription (`Checked.Trust.Transcriptions.agree_DL1z`); its name is not checked (for `q : ℝ`): is defined as `-(1 / 2) * (-1 + q)`
- `DL2z q j k` — PRINTED, not pinned; an independent blind second reading of the source agrees with this transcription (`Checked.Trust.Transcriptions.agree_DL2z`); its name is not checked (for `q : ℝ`, `j : ℝ`, `k : ℝ`): is defined as `-(1 / 6) * (1 - q - 3 * q ^ 2 + j + k)`
- `DL3z q j s k` — PRINTED, not pinned; an independent blind second reading of the source agrees with this transcription (`Checked.Trust.Transcriptions.agree_DL3z`); its name is not checked (for `q : ℝ`, `j : ℝ`, `s : ℝ`, `k : ℝ`): is defined as `1 / 24 * (2 - 2 * q - 15 * q ^ 2 - 15 * q ^ 3 + 5 * j + 10 * q * j + s + 2 * k * (1 + 3 * q))`
- `cosmoCoeff n a t` — **PINNED** (pin theorem `cosmoCoeffCore_pins`): the `n`-th cosmographic coefficient a⁽ⁿ⁾(t)/(a(t)·H(t)ⁿ) of the scale factor `a` at time `t` (n = `n`; j, s, l, m for n = 3, 4, 5, 6; the deceleration parameter is minus the n = 2 coefficient)
- `curvK K a t₀` — **PINNED** (pin theorem `curvKSpec_pins`): the curvature parameter K/(H₀²·a₀²) at time `t₀` for curvature constant `K` and scale factor `a` (c = 1; equal to −Ω_k)
- `decel a t` — **PINNED** (pin theorem `decelSpec_pins`): the deceleration parameter −a″(t)·a(t)/a′(t)² of the scale factor `a` at time `t`
- `hubble a t` — **PINNED** (pin theorem `hubbleSpec_pins`): the Hubble rate a′(t)/a(t) of the scale factor `a` at time `t`
- `lumDist K a t₀ t` — **PINNED** (pin theorem `lumDistSpec2_pins`): the luminosity distance a(t₀)·(1 + z)·S_K(χ), at observation time `t₀`, of a source emitting at time `t`, in the FLRW model with scale factor `a` and curvature constant `K` (c = 1; z the redshift, χ the comoving radial distance, S_K the transverse factor)
- `printedDL4z q j s l k` — PRINTED, not pinned; an independent blind second reading of the source agrees with this transcription (`Checked.Trust.Transcriptions.agree_printedDL4z`); its name is not checked (for `q : ℝ`, `j : ℝ`, `s : ℝ`, `l : ℝ`, `k : ℝ`): is defined as `1 / 120 * (-6 + 6 * q + 81 * q ^ 2 + 165 * q ^ 3 + 105 * q ^ 4 - 110 * q * j - 105 * q ^ 2 * j - 15 * q * s + -27 * j + 10 * j ^ 2 - 11 * s - l - 5 * k * (1 + 8 * q + 9 * q ^ 2 - 2 * j))`
- `redshift a t₀ t` — **PINNED** (pin theorem `redshiftCore_pins`): the redshift a(`t₀`)/a(`t`) − 1, observed at time `t₀`, of light emitted at time `t` (scale factor `a`)
- `remLz D4 K a t₀ t` — COMPOSITE, not pinned, so only the formula shown is checked, not its name (for `D4 : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ`, `K : ℝ`, `a : ℝ → ℝ`, `t₀ : ℝ`, `t : ℝ`): is defined as `hubble a t₀ * lumDist K a t₀ t - seriesZ (DL1z (decel a t₀)) (DL2z (decel a t₀) (cosmoCoeff 3 a t₀) (curvK K a t₀)) (DL3z (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) (curvK K a t₀)) (D4 (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) (cosmoCoeff 5 a t₀) (curvK K a t₀)) (redshift a t₀ t)`
- `seriesZ d1 d2 d3 d4 z` — FORMULA, not pinned; name and body agree with a blind second formulation (`Checked.Trust.Formulations.agree_seriesZ`) (for `d1 : ℝ`, `d2 : ℝ`, `d3 : ℝ`, `d4 : ℝ`, `z : ℝ`): is defined as `z * (1 + d1 * z + d2 * z ^ 2 + d3 * z ^ 3 + d4 * z ^ 4)`

## Author's paraphrase (hand-written; checked only by prose rules)

Milne universe (`a = t`, `K = −1`, `t₀ = 1`; exact `H₀d_L = z + z²/2`): the printed `D⁴_L`
fails from the past (standalone instance; Milne is not positive for all `t`).

## Formal statement (Lean 4)

```lean
theorem milne_printedDL4z_fails_past :
    ¬ (fun t => remLz printedDL4z (-1) (fun t => t) 1 t)
      =o[𝓝[<] 1] (fun t => redshift (fun t => t) 1 t ^ 5) := …
```

## Definitions it uses

See GLOSSARY.md: `Cosmography.Aviles.cosmoCoeff`, `Cosmography.BambaK.lumDist`, `Cosmography.BambaZ.curvK`, `Cosmography.decel`, `Cosmography.hubble`, `Cosmography.redshift`, `Cosmography.BambaZ.DL1z`, `Cosmography.BambaZ.DL2z`, `Cosmography.BambaZ.DL3z`, `Cosmography.BambaZ.printedDL4z`, `Cosmography.BambaY.comoving`, `Cosmography.BambaZ.remLz`, `Cosmography.BambaZ.seriesZ`, `Cosmography.Transverse.transverse`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: cosmoCoeff, lumDist, curvK, decel, hubble, redshift.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): DL1z², DL2z², DL3z², printedDL4z².
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): unconditional.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): remLz: K = -1, t₀ = 1; redshift: t₀ = 1; hubble: t = 1; lumDist: K = -1, t₀ = 1; decel: t = 1; cosmoCoeff: n = 3, t = 1, n = 4, n = 5; curvK: K = -1, t₀ = 1.
- Source file: `Checked/Cosmography/BambaZ.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 25
