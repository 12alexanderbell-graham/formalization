# Item 38

**Area:** F4

**Source:** Bamba, Capozziello, Nojiri, Odintsov, Astrophys. Space Sci. 342, 155 (2012), arXiv:1205.3421 (v1, v2, v3), Eq. (10.54): y-redshift luminosity-distance coefficient D²_{L,y} has the wrong overall sign

## Claim in plain words (the system's own text)

The printed `D²_{L,y}` fails in every flat `C³` model with `a(t₀) ≠ 0`, `H₀ ≠ 0` and
`11 − 5q₀ + 3q₀² − j₀ ≠ 0` (past emission only; the two-sided version follows).

## Formal statement (Lean 4)

```lean
theorem printedD2y_fails_past (a : ℝ → ℝ) (t₀ : ℝ) (ha : ContDiffAt ℝ 3 a t₀)
    (ha0 : a t₀ ≠ 0) (hH : hubble a t₀ ≠ 0)
    (hD : 11 - 5 * decel a t₀ + 3 * decel a t₀ ^ 2 - cosmoCoeff 3 a t₀ ≠ 0) :
    ¬ (fun t => remainderY printedD2y a t₀ t) =o[𝓝[<] t₀] (fun t => yred a t₀ t ^ 3) := …
```

## Definitions it uses

See GLOSSARY.md: `Cosmography.Aviles.cosmoCoeff`, `Cosmography.BambaY.lumDistFlat`, `Cosmography.BambaY.yred`, `Cosmography.decel`, `Cosmography.hubble`, `Cosmography.BambaY.D1y`, `Cosmography.BambaY.printedD2y`, `Cosmography.BambaY.comoving`, `Cosmography.BambaY.remainderY`, `Cosmography.BambaY.seriesY`, `Cosmography.CCS.D2`, `Cosmography.redshift`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: cosmoCoeff, lumDistFlat, yred, decel, hubble.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): D1y², printedD2y².
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): `printedD2y_fails_past`.
- Source file: `Checked/Cosmography/BambaDLy.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 38
