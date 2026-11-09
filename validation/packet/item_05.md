# Item 05

**Area:** F4

**Source:** Bamba, Capozziello, Nojiri, Odintsov, Astrophys. Space Sci. 342, 155 (2012), arXiv:1205.3421 (v1, v2, v3), Eq. (10.54): y-redshift luminosity-distance coefficient D²_{L,y} has the wrong overall sign

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**For every** `a : ℝ → ℝ`, `t₀ : ℝ`:

**assuming**

1. `ContDiffAt ℝ 3 a t₀`
2. `a t₀ ≠ 0`
3. `hubble a t₀ ≠ 0`

**then**

- `(fun t => remainderY correctD2y a t₀ t) =o[nhds t₀] fun t => yred a t₀ t ^ 3`

Program definitions in this claim:

- `D1y q` — PRINTED, not pinned; an independent blind second reading of the source agrees with this transcription (`Checked.Trust.Transcriptions.agree_D1y`); its name is not checked (for `q : ℝ`): is defined as `-(1 / 2) * (-3 + q)`
- `correctD2y q j Ω` — FORMULA, not pinned; name and body agree with a blind second formulation (`Checked.Trust.Formulations.agree_correctD2y`) (for `q : ℝ`, `j : ℝ`, `Ω : ℝ`): is defined as `1 / 6 * (12 - 5 * q + 3 * q ^ 2 - j - Ω)`
- `cosmoCoeff n a t` — **PINNED** (pin theorem `cosmoCoeffCore_pins`): phrase (hand-written, linted): the cosmographic coefficient of the scale factor `a` at the time of evaluation `t` for the derivative order of the coefficient `n` (j, s, l, m for the orders 3, 4, 5, 6; the deceleration parameter is minus the order 2 coefficient); by definition, `cosmoCoeff n a t` is `iteratedDeriv n a t / (a t * hubble a t ^ n)`
- `decel a t` — **PINNED** (pin theorem `decelSpec_pins`): phrase (hand-written, linted): the deceleration parameter of the scale factor `a` at the cosmic time of evaluation `t` (minus acceleration times scale factor over velocity squared); by definition, `decel a t` is `-(deriv (deriv a) t * a t) / deriv a t ^ 2`
- `hubble a t` — **PINNED** (pin theorem `hubbleSpec_pins`): phrase (hand-written, linted): the Hubble rate of the scale factor `a` at the cosmic time of evaluation `t`; by definition, `hubble a t` is `deriv a t / a t`
- `lumDistFlat a t₀ t` — **PINNED** (pin theorem `lumDistFlat_pins`): phrase (hand-written, linted): the luminosity distance in flat FLRW, at the observation time `t₀`, of a source at the emission time `t` (scale factor `a`; units in which the speed of light is one); by definition, `lumDistFlat a t₀ t` is `a t₀ * (1 + redshift a t₀ t) * comoving a t₀ t`
- `remainderY D2 a t₀ t` — COMPOSITE, not pinned, so only the formula shown is checked, not its name (for `D2 : ℝ → ℝ → ℝ → ℝ`, `a : ℝ → ℝ`, `t₀ : ℝ`, `t : ℝ`): is defined as `hubble a t₀ * lumDistFlat a t₀ t - seriesY (D2 (decel a t₀) (cosmoCoeff 3 a t₀) 1) (decel a t₀) (yred a t₀ t)`
- `seriesY d2 q y` — FORMULA, not pinned; name and body agree with a blind second formulation (`Checked.Trust.Formulations.agree_seriesY`) (for `d2 : ℝ`, `q : ℝ`, `y : ℝ`): is defined as `y * (1 + D1y q * y + d2 * y ^ 2)`
- `yred a t₀ t` — **PINNED** (pin theorem `yRedSpec_pins`): phrase (hand-written, linted): the y-redshift at the observation time `t₀` of light at the emission time `t` (scale factor `a`; positive for redshift, negative for blueshift); by definition, `yred a t₀ t` is `redshift a t₀ t / (1 + redshift a t₀ t)`

## Author's paraphrase (hand-written; checked only by prose rules)

**Luminosity distance to third order in `y`** (FLRW of any spatial curvature `K`, correct `D²_{L,y}`): for every
scale factor that is `C³` at `t₀`, with `a(t₀) ≠ 0` and `H₀ ≠ 0`.

## Formal statement (Lean 4)

```lean
theorem lumDist_y_third_order (a : ℝ → ℝ) (t₀ : ℝ) (ha : ContDiffAt ℝ 3 a t₀)
    (ha0 : a t₀ ≠ 0) (hH : hubble a t₀ ≠ 0) :
    (fun t => remainderY correctD2y a t₀ t) =o[𝓝 t₀] (fun t => yred a t₀ t ^ 3) := …
```

## Definitions it uses

See GLOSSARY.md: `Cosmography.Aviles.cosmoCoeff`, `Cosmography.BambaY.lumDistFlat`, `Cosmography.BambaY.yred`, `Cosmography.decel`, `Cosmography.hubble`, `Cosmography.BambaY.D1y`, `Cosmography.BambaY.comoving`, `Cosmography.BambaY.correctD2y`, `Cosmography.BambaY.remainderY`, `Cosmography.BambaY.seriesY`, `Cosmography.CCS.D2`, `Cosmography.redshift`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: cosmoCoeff, lumDistFlat, yred, decel, hubble.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): D1y².
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): `lumDist_y_third_order`.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): cosmoCoeff: n = 3.
- Source file: `Checked/Cosmography/BambaDLy.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 05
