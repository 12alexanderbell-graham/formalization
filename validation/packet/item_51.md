# Item 51

**Area:** F10

**Source:** Bamba, Capozziello, Nojiri, Odintsov, Astrophys. Space Sci. 342, 155 (2012), arXiv:1205.3421, Sec. XI, Eqs. (11.42)–(11.45) (p. 121), from Capozziello, Cardone, Salzano 2008 (arXiv:0802.1583) Eqs. (43)–(44) and the display after (44): the first-order deviations η₂₀ = F″(R₀)H₀⁴/F(R₀), η₃₀ = F‴(R₀)H₀⁶/F(R₀) of F(R) from GR are wrong, formulas and numbers

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**It holds that**

1. `correct20 (41 / 1000) ∈ Set.Ioo (-0.25) (-0.24)`
2. `correct20 (1 / 4) ∈ Set.Ioo (-33e-3) (-31e-3)`
3. `correct30 (41 / 1000) ∈ Set.Ioo (-0.41) (-0.39)`
4. `correct30 (1 / 4) ∈ Set.Ioo (-16e-3) (-15e-3)`

Program definitions in this claim:

- `correct20 Ω` — FORMULA, not pinned; name and body agree with a blind second formulation (`Checked.Trust.Formulations.agree_correct20`) (for `Ω : ℝ`): is defined as `-2 * (27 * Ω ^ 2 + 24 * Ω - 32) / (27 * Ω * (Ω - 2) * (27 * Ω ^ 2 + 60 * Ω + 112))`
- `correct30 Ω` — FORMULA, not pinned; name and body agree with a blind second formulation (`Checked.Trust.Formulations.agree_correct30`) (for `Ω : ℝ`): is defined as `-2 * (81 * Ω ^ 2 - 60 * Ω - 16) / (243 * Ω ^ 2 * (Ω - 2) * (27 * Ω ^ 2 + 60 * Ω + 112))`

## Author's paraphrase (hand-written; checked only by prose rules)

**Correct (11.44)–(11.45)** at the paper's fiducial values: `η₂₀ ≈ −0.249ε, −0.032ε`;
`η₃₀ ≈ −0.400ε, −0.0152ε` (printed: `0.15ε, −0.12ε`; `4ε, −0.18ε`).

## Formal statement (Lean 4)

```lean
theorem eta_numbers :
    correct20 (41 / 1000) ∈ Set.Ioo (-0.25) (-0.24) ∧
    correct20 (1 / 4) ∈ Set.Ioo (-0.033) (-0.031) ∧
    correct30 (41 / 1000) ∈ Set.Ioo (-0.41) (-0.39) ∧
    correct30 (1 / 4) ∈ Set.Ioo (-0.016) (-0.015) := …
```

## Definitions it uses

See GLOSSARY.md: `Cosmography.FREta.correct20`, `Cosmography.FREta.correct30`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: —.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): —.
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): unconditional.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): correct20: Ω = 41/1000, Ω = 1/4; correct30: Ω = 41/1000, Ω = 1/4.
- Source file: `Checked/Cosmography/FREta.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 51
