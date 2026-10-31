# Item 16

**Area:** F9

**Source:** Bamba, Capozziello, Nojiri, Odintsov, Astrophys. Space Sci. 342, 155 (2012), arXiv:1205.3421, Sec. XI ("testing F(R) gravity by cosmography"), Eq. (11.31), from Capozziello, Cardone, Salzano 2008 (arXiv:0802.1583, PRD 78, 063504) Eq. (33): the common denominator R of the F(R₀), F″(R₀), F‴(R₀) formulas is wrong, so the printed F(R₀) formula (11.21) fails the paper's own ΛCDM check (11.40); also (11.13) d³R₀/dt³ has a sign error

## Claim in plain words (the system's own text)

Division form at every `Ω ∈ (0,1)` where the printed `R` is nonzero in ΛCDM
(`printedR` at ΛCDM is `−(243Ω⁴ + 540Ω³ − 6264Ω² + 9360Ω − 3328)/16`).

## Formal statement (Lean 4)

```lean
theorem printedF0_false_at {Ω : ℝ} (h0 : 0 < Ω) (h1 : Ω < 1)
    (hR : 243 * Ω ^ 4 + 540 * Ω ^ 3 - 6264 * Ω ^ 2 + 9360 * Ω - 3328 ≠ 0) :
    ¬ ∀ (a F : ℝ → ℝ) (t₀ : ℝ), IsFRCosmo Ω a F t₀ →
      printedR (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) (cosmoCoeff 5 a t₀) ≠ 0 →
      F (curv a t₀) / (6 * hubble a t₀ ^ 2) =
        -(P0 (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) (cosmoCoeff 5 a t₀) * Ω
            + Q0 (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) (cosmoCoeff 5 a t₀))
          / printedR (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) (cosmoCoeff 5 a t₀) := …
```

## Definitions it uses

See GLOSSARY.md: `Cosmography.Aviles.cosmoCoeff`, `Cosmography.FRCosmo.FriedmannEq`, `Cosmography.FRCosmo.MasterEq`, `Cosmography.FRCosmo.curv`, `Cosmography.decel`, `Cosmography.hubble`, `Cosmography.FRCosmo.P0`, `Cosmography.FRCosmo.Q0`, `Cosmography.FRCosmo.printedR`, `Cosmography.FRCosmo.IsFRCosmo`, `Cosmography.FRCosmo.rhoM`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: cosmoCoeff, FriedmannEq, MasterEq, curv, decel, hubble.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): P0², Q0², printedR².
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): `printedF0_false_at`.
- Source file: `Checked/Cosmography/FRCosmo.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 16
