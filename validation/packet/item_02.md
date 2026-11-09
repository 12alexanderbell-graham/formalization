# Item 02

**Area:** F6

**Source:** Bamba, Capozziello, Nojiri, Odintsov, Astrophys. Space Sci. 342, 155 (2012), arXiv:1205.3421 (v1–v3), Eqs. (10.55)–(10.57), copied verbatim from Capozziello & Salzano, Adv. Astron. 2009, 217420, arXiv:0902.0088, Eqs. (56)–(58): curvature terms of the y-redshift d_L coefficients D³_{L,y}, D⁴_{L,y} wrong

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**For every** `K : ℝ`, `a : ℝ → ℝ`, `t₀ : ℝ`:

**assuming**

1. `ContDiffAt ℝ 5 a t₀`
2. `a t₀ ≠ 0`
3. `hubble a t₀ ≠ 0`

**then**

- `(fun t => remK correctD2y correctD3y correctD4y K a t₀ t) =o[nhds t₀] fun t => yred a t₀ t ^ 5`

Program definitions in this claim:

- `D1y q` — PRINTED, not pinned; an independent blind second reading of the source agrees with this transcription (`Checked.Trust.Transcriptions.agree_D1y`); its name is not checked (for `q : ℝ`): is defined as `-(1 / 2) * (-3 + q)`
- `correctD2y q j Ω` — FORMULA, not pinned; name and body agree with a blind second formulation (`Checked.Trust.Formulations.agree_correctD2y`) (for `q : ℝ`, `j : ℝ`, `Ω : ℝ`): is defined as `1 / 6 * (12 - 5 * q + 3 * q ^ 2 - j - Ω)`
- `correctD3y q j s Ω` — FORMULA, not pinned; name and body agree with a blind second formulation (`Checked.Trust.Formulations.agree_correctD3y`) (for `q : ℝ`, `j : ℝ`, `s : ℝ`, `Ω : ℝ`): is defined as `printedD3y q j s Ω + (Ω - 1) * (3 * q - 2) / 6`
- `correctD4y q j s l Ω` — FORMULA, not pinned; name and body agree with a blind second formulation (`Checked.Trust.Formulations.agree_correctD4y`) (for `q : ℝ`, `j : ℝ`, `s : ℝ`, `l : ℝ`, `Ω : ℝ`): is defined as `printedD4y q j s l Ω + (Ω - 1) ^ 2 / 120 + 5 * q * (Ω - 1) / 12`
- `cosmoCoeff n a t` — **PINNED** (pin theorem `cosmoCoeffCore_pins`): phrase (hand-written, linted): the cosmographic coefficient of the scale factor `a` at the time of evaluation `t` for the derivative order of the coefficient `n` (j, s, l, m for the orders 3, 4, 5, 6; the deceleration parameter is minus the order 2 coefficient); by definition, `cosmoCoeff n a t` is `iteratedDeriv n a t / (a t * hubble a t ^ n)`
- `decel a t` — **PINNED** (pin theorem `decelSpec_pins`): phrase (hand-written, linted): the deceleration parameter of the scale factor `a` at the cosmic time of evaluation `t` (minus acceleration times scale factor over velocity squared); by definition, `decel a t` is `-(deriv (deriv a) t * a t) / deriv a t ^ 2`
- `hubble a t` — **PINNED** (pin theorem `hubbleSpec_pins`): phrase (hand-written, linted): the Hubble rate of the scale factor `a` at the cosmic time of evaluation `t`; by definition, `hubble a t` is `deriv a t / a t`
- `lumDist K a t₀ t` — **PINNED** (pin theorem `lumDistSpec2_pins`): phrase (hand-written, linted): the luminosity distance in FLRW with curvature, at the observation time `t₀`, of a source at the emission time `t`, in the model with scale factor `a` and spatial curvature constant `K` (units in which the speed of light is one; positive curvature constant means closed, negative means open); by definition, `lumDist K a t₀ t` is `a t₀ * (1 + redshift a t₀ t) * transverse K (comoving a t₀ t)`
- `omega0 K a t₀` — **PINNED** (pin theorem `omega0Spec_pins`): phrase (hand-written, linted): the present total density parameter Ω₀ at the observation time `t₀` for spatial curvature constant `K` and scale factor `a` (units in which the speed of light is one; one plus curvature term, positive curvature constant gives above one; Ω_k is one minus Ω₀); by definition, `omega0 K a t₀` is `1 + K / (hubble a t₀ ^ 2 * a t₀ ^ 2)`
- `printedD3y q j s Ω` — PRINTED, not pinned; an independent blind second reading of the source agrees with this transcription (`Checked.Trust.Transcriptions.agree_printedD3y`); its name is not checked (for `q : ℝ`, `j : ℝ`, `s : ℝ`, `Ω : ℝ`): is defined as `1 / 24 * (52 - 20 * q + 21 * q ^ 2 - 15 * q ^ 3 - 7 * j + 10 * q * j + s - 2 * Ω * (1 + 3 * q))`
- `printedD4y q j s l Ω` — PRINTED, not pinned; an independent blind second reading of the source agrees with this transcription (`Checked.Trust.Transcriptions.agree_printedD4y`); its name is not checked (for `q : ℝ`, `j : ℝ`, `s : ℝ`, `l : ℝ`, `Ω : ℝ`): is defined as `1 / 120 * (359 - 184 * q + 186 * q ^ 2 - 135 * q ^ 3 + 105 * q ^ 4 + 90 * q * j - 105 * q ^ 2 * j - 15 * q * s + -57 * j + 10 * j ^ 2 + 9 * s - l - 5 * Ω * (17 - 6 * q + 9 * q ^ 2 - 2 * j))`
- `remK D2 D3 D4 K a t₀ t` — COMPOSITE, not pinned, so only the formula shown is checked, not its name (for `D2 : ℝ → ℝ → ℝ → ℝ`, `D3 : ℝ → ℝ → ℝ → ℝ → ℝ`, `D4 : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ`, `K : ℝ`, `a : ℝ → ℝ`, `t₀ : ℝ`, `t : ℝ`): is defined as `hubble a t₀ * lumDist K a t₀ t - seriesY4 (decel a t₀) (D2 (decel a t₀) (cosmoCoeff 3 a t₀) (omega0 K a t₀)) (D3 (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) (omega0 K a t₀)) (D4 (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) (cosmoCoeff 5 a t₀) (omega0 K a t₀)) (yred a t₀ t)`
- `seriesY4 q d2 d3 d4 y` — FORMULA, not pinned; name and body agree with a blind second formulation (`Checked.Trust.Formulations.agree_seriesY4`) (for `q : ℝ`, `d2 : ℝ`, `d3 : ℝ`, `d4 : ℝ`, `y : ℝ`): is defined as `y * (1 + D1y q * y + d2 * y ^ 2 + d3 * y ^ 3 + d4 * y ^ 4)`
- `yred a t₀ t` — **PINNED** (pin theorem `yRedSpec_pins`): phrase (hand-written, linted): the y-redshift at the observation time `t₀` of light at the emission time `t` (scale factor `a`; positive for redshift, negative for blueshift); by definition, `yred a t₀ t` is `redshift a t₀ t / (1 + redshift a t₀ t)`

## Author's paraphrase (hand-written; checked only by prose rules)

**Headline.** Luminosity distance to fifth order in `y` for every curvature `K`
and every scale factor that is `C⁵` at `t₀` with `a(t₀) ≠ 0`, `H₀ ≠ 0`.

## Formal statement (Lean 4)

```lean
theorem lumDist_y_fifth_order (K : ℝ) (a : ℝ → ℝ) (t₀ : ℝ) (ha : ContDiffAt ℝ 5 a t₀)
    (ha0 : a t₀ ≠ 0) (hH : hubble a t₀ ≠ 0) :
    (fun t => remK correctD2y correctD3y correctD4y K a t₀ t) =o[𝓝 t₀]
      (fun t => yred a t₀ t ^ 5) := …
```

## Definitions it uses

See GLOSSARY.md: `Cosmography.Aviles.cosmoCoeff`, `Cosmography.BambaK.lumDist`, `Cosmography.BambaK.omega0`, `Cosmography.BambaY.yred`, `Cosmography.decel`, `Cosmography.hubble`, `Cosmography.BambaK.printedD3y`, `Cosmography.BambaK.printedD4y`, `Cosmography.BambaY.D1y`, `Cosmography.BambaK.correctD3y`, `Cosmography.BambaK.correctD4y`, `Cosmography.BambaK.remK`, `Cosmography.BambaK.seriesY4`, `Cosmography.BambaY.comoving`, `Cosmography.BambaY.correctD2y`, `Cosmography.CCS.D2`, `Cosmography.CCS.D3`, `Cosmography.Transverse.transverse`, `Cosmography.redshift`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: cosmoCoeff, lumDist, omega0, yred, decel, hubble.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): printedD3y², printedD4y², D1y².
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): `lumDist_y_fifth_order`.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): cosmoCoeff: n = 3, n = 4, n = 5.
- Source file: `Checked/Cosmography/BambaCurved.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 02
