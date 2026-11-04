# Item 27

**Area:** F6

**Source:** Bamba, Capozziello, Nojiri, Odintsov, Astrophys. Space Sci. 342, 155 (2012), arXiv:1205.3421 (v1–v3), Eqs. (10.55)–(10.57), copied verbatim from Capozziello & Salzano, Adv. Astron. 2009, 217420, arXiv:0902.0088, Eqs. (56)–(58): curvature terms of the y-redshift d_L coefficients D³_{L,y}, D⁴_{L,y} wrong

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**For every** `K : ℝ`, `a : ℝ → ℝ`, `t₀ : ℝ`:

**assuming**

1. `ContDiffAt ℝ 5 a t₀`
2. `a t₀ ≠ 0`
3. `hubble a t₀ ≠ 0`
4. `(omega0 K a t₀ - 1) * (3 * decel a t₀ - 2) ≠ 0`

**then**

- it is false that (`(fun t => remK correctD2y printedD3y (fun x x_1 x_2 x_3 x_4 => 0) K a t₀ t) =o[nhdsWithin t₀ (Set.Iio t₀)] fun t => yred a t₀ t ^ 4`)

Program definitions in this claim:

- `D1y q` — PRINTED, not pinned (for `q : ℝ`): is defined as `-(1 / 2) * (-3 + q)`
- `correctD2y q j Ω` — FORMULA, not pinned (for `q : ℝ`, `j : ℝ`, `Ω : ℝ`): is defined as `1 / 6 * (12 - 5 * q + 3 * q ^ 2 - j - Ω)`
- `cosmoCoeff n a t` — **PINNED** (pin theorem `cosmoCoeffCore_pins`): the `n`-th cosmographic coefficient a⁽ⁿ⁾(t)/(a(t)·H(t)ⁿ) of the scale factor `a` at time `t` (n = `n`; j, s, l, m for n = 3, 4, 5, 6; the deceleration parameter is minus the n = 2 coefficient)
- `decel a t` — **PINNED** (pin theorem `decelSpec_pins`): the deceleration parameter −a″(t)·a(t)/a′(t)² of the scale factor `a` at time `t`
- `hubble a t` — **PINNED** (pin theorem `hubbleSpec_pins`): the Hubble rate a′(t)/a(t) of the scale factor `a` at time `t`
- `lumDist K a t₀ t` — **PINNED** (pin theorem `lumDistSpec2_pins`): the luminosity distance a(t₀)·(1 + z)·S_K(χ), at observation time `t₀`, of a source emitting at time `t`, in the FLRW model with scale factor `a` and curvature constant `K` (c = 1; z the redshift, χ the comoving radial distance, S_K the transverse factor)
- `omega0 K a t₀` — **PINNED** (pin theorem `omega0Spec_pins`): the total density parameter Ω₀ = 1 + K/(H₀²·a₀²) at time `t₀` for curvature constant `K` and scale factor `a` (c = 1; H₀, a₀ the Hubble rate and scale factor at `t₀`; Ω_k = 1 − Ω₀)
- `printedD3y q j s Ω` — PRINTED, not pinned (for `q : ℝ`, `j : ℝ`, `s : ℝ`, `Ω : ℝ`): is defined as `1 / 24 * (52 - 20 * q + 21 * q ^ 2 - 15 * q ^ 3 - 7 * j + 10 * q * j + s - 2 * Ω * (1 + 3 * q))`
- `remK D2 D3 D4 K a t₀ t` — COMPOSITE, not pinned (for `D2 : ℝ → ℝ → ℝ → ℝ`, `D3 : ℝ → ℝ → ℝ → ℝ → ℝ`, `D4 : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ`, `K : ℝ`, `a : ℝ → ℝ`, `t₀ : ℝ`, `t : ℝ`): is defined as `hubble a t₀ * lumDist K a t₀ t - seriesY4 (decel a t₀) (D2 (decel a t₀) (cosmoCoeff 3 a t₀) (omega0 K a t₀)) (D3 (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) (omega0 K a t₀)) (D4 (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) (cosmoCoeff 5 a t₀) (omega0 K a t₀)) (yred a t₀ t)`
- `seriesY4 q d2 d3 d4 y` — FORMULA, not pinned (for `q : ℝ`, `d2 : ℝ`, `d3 : ℝ`, `d4 : ℝ`, `y : ℝ`): is defined as `y * (1 + D1y q * y + d2 * y ^ 2 + d3 * y ^ 3 + d4 * y ^ 4)`
- `yred a t₀ t` — **PINNED** (pin theorem `yRedSpec_pins`): the y-redshift z/(1 + z), observed at time `t₀`, of light emitted at time `t` (scale factor `a`)

## Author's paraphrase (hand-written; checked only by prose rules)

The printed `D³_{L,y}` (with the corrected `D²`) fails, from the past, in every `C⁵` model
with `a(t₀) ≠ 0`, `H₀ ≠ 0`, `Ω₀ ≠ 1` and `q₀ ≠ 2/3`.

## Formal statement (Lean 4)

```lean
theorem printedD3y_fails_past (K : ℝ) (a : ℝ → ℝ) (t₀ : ℝ) (ha : ContDiffAt ℝ 5 a t₀)
    (ha0 : a t₀ ≠ 0) (hH : hubble a t₀ ≠ 0)
    (hD : (omega0 K a t₀ - 1) * (3 * decel a t₀ - 2) ≠ 0) :
    ¬ (fun t => remK correctD2y printedD3y (fun _ _ _ _ _ => 0) K a t₀ t)
      =o[𝓝[<] t₀] (fun t => yred a t₀ t ^ 4) := …
```

## Definitions it uses

See GLOSSARY.md: `Cosmography.Aviles.cosmoCoeff`, `Cosmography.BambaK.lumDist`, `Cosmography.BambaK.omega0`, `Cosmography.BambaY.yred`, `Cosmography.decel`, `Cosmography.hubble`, `Cosmography.BambaK.printedD3y`, `Cosmography.BambaY.D1y`, `Chemistry.RKReduced.q`, `Cosmography.BambaK.remK`, `Cosmography.BambaK.seriesY4`, `Cosmography.BambaY.comoving`, `Cosmography.BambaY.correctD2y`, `Cosmography.CCS.D2`, `Cosmography.CCS.D3`, `Cosmography.Transverse.transverse`, `Cosmography.redshift`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: cosmoCoeff, lumDist, omega0, yred, decel, hubble.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): printedD3y², D1y².
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): `printedD3y_fails_past`.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): cosmoCoeff: n = 3, n = 4, n = 5.
- Source file: `Checked/Cosmography/BambaCurved.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 27
