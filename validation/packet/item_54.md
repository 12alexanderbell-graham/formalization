# Item 54

**Area:** F5

**Source:** Cattoën & Visser, Class. Quantum Grav. 24, 5985 (2007), arXiv:0710.1887v1, Eq. (59) (also gr-qc/0703122 v1–v3 and arXiv:0809.0537v1 Eq. (32)): deceleration-distance y² coefficient 1/12 should be 1/24

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**For every** `a : ℝ → ℝ`, `t₀ : ℝ`:

**assuming**

1. `ContDiffAt ℝ 3 a t₀`
2. `a t₀ ≠ 0`
3. `hubble a t₀ ≠ 0`

**then**

- `(fun t => remainderQ correctQ2 a t₀ t) =o[nhds t₀] fun t => yred a t₀ t ^ 3`

Program definitions in this claim:

- `correctQ2 q j Ω` — FORMULA, not pinned; name and body agree with a blind second formulation (`Checked.Trust.Formulations.agree_correctQ2`) (for `q : ℝ`, `j : ℝ`, `Ω : ℝ`): is defined as `1 / 24 * (3 - 2 * q + 12 * q ^ 2 - 4 * (j + Ω))`
- `cosmoCoeff n a t` — **PINNED** (pin theorem `cosmoCoeffCore_pins`): phrase (hand-written, linted): the cosmographic coefficient of the scale factor `a` at the time of evaluation `t` for the derivative order of the coefficient `n` (j, s, l, m for the orders 3, 4, 5, 6; the deceleration parameter is minus the order 2 coefficient); by definition, `cosmoCoeff n a t` is `iteratedDeriv n a t / (a t * hubble a t ^ n)`
- `dQFlat a t₀ t` — PRINTED, not pinned; an independent blind second reading of the source agrees with this transcription (`Checked.Trust.Transcriptions.agree_dQFlat`); its name is not checked (for `a : ℝ → ℝ`, `t₀ : ℝ`, `t : ℝ`): is defined as `lumDistFlat a t₀ t / (1 + redshift a t₀ t) ^ (3 / 2)`
- `decel a t` — **PINNED** (pin theorem `decelSpec_pins`): phrase (hand-written, linted): the deceleration parameter of the scale factor `a` at the cosmic time of evaluation `t` (minus acceleration times scale factor over velocity squared); by definition, `decel a t` is `-(deriv (deriv a) t * a t) / deriv a t ^ 2`
- `hubble a t` — **PINNED** (pin theorem `hubbleSpec_pins`): phrase (hand-written, linted): the Hubble rate of the scale factor `a` at the cosmic time of evaluation `t`; by definition, `hubble a t` is `deriv a t / a t`
- `lumDistFlat a t₀ t` — **PINNED** (pin theorem `lumDistFlat_pins`): phrase (hand-written, linted): the luminosity distance in flat FLRW, at the observation time `t₀`, of a source at the emission time `t` (scale factor `a`; units in which the speed of light is one); by definition, `lumDistFlat a t₀ t` is `a t₀ * (1 + redshift a t₀ t) * comoving a t₀ t`
- `redshift a t₀ t` — **PINNED** (pin theorem `redshiftCore_pins`): phrase (hand-written, linted): the cosmological redshift at the observation time `t₀` of light at the emission time `t` (scale factor `a`; positive when emission precedes observation in an expanding universe); by definition, `redshift a t₀ t` is `a t₀ / a t - 1`
- `remainderQ D2 a t₀ t` — COMPOSITE, not pinned, so only the formula shown is checked, not its name (for `D2 : ℝ → ℝ → ℝ → ℝ`, `a : ℝ → ℝ`, `t₀ : ℝ`, `t : ℝ`): is defined as `hubble a t₀ * dQFlat a t₀ t - seriesQ (D2 (decel a t₀) (cosmoCoeff 3 a t₀) 1) (decel a t₀) (yred a t₀ t)`
- `seriesQ d2 q y` — FORMULA, not pinned; name and body agree with a blind second formulation (`Checked.Trust.Formulations.agree_seriesQ`) (for `d2 : ℝ`, `q : ℝ`, `y : ℝ`): is defined as `y * (1 - q / 2 * y + d2 * y ^ 2)`
- `yred a t₀ t` — **PINNED** (pin theorem `yRedSpec_pins`): phrase (hand-written, linted): the y-redshift at the observation time `t₀` of light at the emission time `t` (scale factor `a`; positive for redshift, negative for blueshift); by definition, `yred a t₀ t` is `redshift a t₀ t / (1 + redshift a t₀ t)`

## Author's paraphrase (hand-written; checked only by prose rules)

**Deceleration distance to third order in `y`** (flat FLRW, coefficient over 24).

## Formal statement (Lean 4)

```lean
theorem dQ_y_third_order (a : ℝ → ℝ) (t₀ : ℝ) (ha : ContDiffAt ℝ 3 a t₀)
    (ha0 : a t₀ ≠ 0) (hH : hubble a t₀ ≠ 0) :
    (fun t => remainderQ correctQ2 a t₀ t) =o[𝓝 t₀] (fun t => yred a t₀ t ^ 3) := …
```

## Definitions it uses

See GLOSSARY.md: `Cosmography.Aviles.cosmoCoeff`, `Cosmography.BambaY.lumDistFlat`, `Cosmography.BambaY.yred`, `Cosmography.decel`, `Cosmography.hubble`, `Cosmography.redshift`, `Cosmography.CVdQ.dQFlat`, `Cosmography.BambaY.comoving`, `Cosmography.CCS.D2`, `Cosmography.CVdQ.correctQ2`, `Cosmography.CVdQ.remainderQ`, `Cosmography.CVdQ.seriesQ`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: cosmoCoeff, lumDistFlat, yred, decel, hubble, redshift.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): dQFlat².
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): `dQ_y_third_order`.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): cosmoCoeff: n = 3.
- Source file: `Checked/Cosmography/CVdQ.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 54
