# Item 32

**Area:** F6

**Source:** Bamba, Capozziello, Nojiri, Odintsov, Astrophys. Space Sci. 342, 155 (2012), arXiv:1205.3421 (v1–v3), Eqs. (10.55)–(10.57), copied verbatim from Capozziello & Salzano, Adv. Astron. 2009, 217420, arXiv:0902.0088, Eqs. (56)–(58): curvature terms of the y-redshift d_L coefficients D³_{L,y}, D⁴_{L,y} wrong

## Claim in plain words (the system's own text)

The printed `D⁴_{L,y}` (with corrected `D²`, `D³`) fails, from the past, in every `C⁵` model
with `a(t₀) ≠ 0`, `H₀ ≠ 0` and `(Ω₀ − 1)²/120 + 5 q₀ (Ω₀ − 1)/12 ≠ 0`.

## Formal statement (Lean 4)

```lean
theorem printedD4y_fails_past (K : ℝ) (a : ℝ → ℝ) (t₀ : ℝ) (ha : ContDiffAt ℝ 5 a t₀)
    (ha0 : a t₀ ≠ 0) (hH : hubble a t₀ ≠ 0)
    (hD : (omega0 K a t₀ - 1) ^ 2 / 120 + 5 * decel a t₀ * (omega0 K a t₀ - 1) / 12 ≠ 0) :
    ¬ (fun t => remK correctD2y correctD3y printedD4y K a t₀ t)
      =o[𝓝[<] t₀] (fun t => yred a t₀ t ^ 5) := …
```

## Definitions it uses

See GLOSSARY.md: `Cosmography.Aviles.cosmoCoeff`, `Cosmography.BambaK.lumDist`, `Cosmography.BambaK.omega0`, `Cosmography.BambaY.yred`, `Cosmography.decel`, `Cosmography.hubble`, `Cosmography.BambaK.printedD3y`, `Cosmography.BambaK.printedD4y`, `Cosmography.BambaY.D1y`, `Cosmography.BambaK.correctD3y`, `Cosmography.BambaK.remK`, `Cosmography.BambaK.seriesY4`, `Cosmography.BambaY.comoving`, `Cosmography.BambaY.correctD2y`, `Cosmography.CCS.D2`, `Cosmography.CCS.D3`, `Cosmography.Transverse.transverse`, `Cosmography.redshift`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: cosmoCoeff, lumDist, omega0, yred, decel, hubble.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): printedD3y², printedD4y², D1y².
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): `printedD4y_fails_past`.
- Source file: `Checked/Cosmography/BambaCurved.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 32
