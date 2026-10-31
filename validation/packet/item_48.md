# Item 48

**Area:** F7

**Source:** Bamba, Capozziello, Nojiri, Odintsov, Astrophys. Space Sci. 342, 155 (2012), arXiv:1205.3421, Eqs. (10.61)–(10.63), verbatim from Capozziello & Salzano 2009 Eqs. (62)–(64): curvature terms of the y-redshift angular-diameter-distance coefficients D³_{A,y}, D⁴_{A,y} wrong

## Claim in plain words (the system's own text)

The printed `D³_{A,y}` (Eq. (10.61)) fails in every FLRW model of curvature `K` whose scale factor is
`C⁵` at `t₀` with `a(t₀) ≠ 0`, `H₀ ≠ 0`, `q₀ ≠ 0` and `Ω₀ ≠ 1`: the `d_A(y)` series is not
`d_A + o(y⁴)` as `t → t₀` (two-sided; past-only: `printedDA3_fails_past`).

## Formal statement (Lean 4)

```lean
theorem printedDA3_fails (K : ℝ) (a : ℝ → ℝ) (t₀ : ℝ) (ha : ContDiffAt ℝ 5 a t₀)
    (ha0 : a t₀ ≠ 0) (hH : hubble a t₀ ≠ 0) (hD : decel a t₀ * (omega0 K a t₀ - 1) ≠ 0) :
    ¬ (fun t => remA printedDA3 (fun _ _ _ _ _ => 0) K a t₀ t)
      =o[𝓝 t₀] (fun t => yred a t₀ t ^ 4) := …
```

## Definitions it uses

See GLOSSARY.md: `Cosmography.Aviles.cosmoCoeff`, `Cosmography.BambaA.angDist`, `Cosmography.BambaK.omega0`, `Cosmography.BambaY.yred`, `Cosmography.decel`, `Cosmography.hubble`, `Cosmography.BambaA.DA1`, `Cosmography.BambaA.DA2`, `Cosmography.BambaA.printedDA3`, `Cosmography.BambaA.remA`, `Cosmography.BambaK.lumDist`, `Cosmography.BambaY.comoving`, `Cosmography.CCS.D3`, `Cosmography.Transverse.transverse`, `Cosmography.redshift`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: cosmoCoeff, angDist, omega0, yred, decel, hubble.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): DA1², DA2², printedDA3².
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): `printedDA3_fails`.
- Source file: `Checked/Cosmography/BambaAngular.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 48
