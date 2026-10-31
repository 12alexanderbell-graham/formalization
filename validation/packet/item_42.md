# Item 42

**Area:** Certified numbers of the findings

**Source:** Capozziello, Cardone, Salzano, PRD 78, 063504 (2008), arXiv:0802.1583v2, App. A, Eq. (A2): lookback-distance z⁵ coefficient, 7/2 q₀⁴ should be 7/8 q₀⁴

## Claim in plain words (the system's own text)

In every flat ΛCDM model with `Ω_m = 0.3` (q₀ = −0.55): the correct lookback `D⁴` is
`0.4555`, the printed one `0.2153`, the excess `printed − correct` is `0.24`, and `q₀ = −0.55`.

## Formal statement (Lean 4)

```lean
theorem F3_D4_LCDM (a : ℝ → ℝ) (t₀ : ℝ) (hL : IsFlatLCDM (3 / 10) a t₀)
    (hs : ContDiffAt ℝ 6 a t₀) :
    RoundsTo (CCS.correctD4 (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀)
      (cosmoCoeff 5 a t₀)) 0.2153 4 ∧
    RoundsTo (CCS.printedD4 (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀)
      (cosmoCoeff 5 a t₀)) 0.4555 4 ∧
    RoundsTo (CCS.printedD4 (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀)
      (cosmoCoeff 5 a t₀) - CCS.correctD4 (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀)
      (cosmoCoeff 5 a t₀)) 0.24 2 ∧
    RoundsTo (decel a t₀) (-0.55) 2 := …
```

## Definitions it uses

See GLOSSARY.md: `Cosmography.Aviles.IsFlatLCDM`, `Cosmography.Aviles.cosmoCoeff`, `Cosmography.decel`, `Cosmography.CCS.printedD4`, `Cosmography.CCS.correctD4`, `Cosmography.hubble`, `Cosmography.redshift`, `Records.RoundsTo`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: IsFlatLCDM, cosmoCoeff, decel.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): printedD4².
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): `F3_D4_LCDM`.
- Source file: `Checked/Records/Findings.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 42
