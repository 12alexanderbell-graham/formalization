# Item 32

**Area:** F2

**Source:** Capozziello, Lazkoz, Salzano, PRD 84, 124061 (2011), arXiv:1104.3096 (v1 and v2), Eq. (22): flat matter + CPL l₀, w_a² term missing a factor 9

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**For every** `Ω : ℝ`, `w₀ : ℝ`, `wₐ : ℝ`:

**then**

- there is `a : ℝ → ℝ` such that (the scale factor `a` obeys the flat matter + CPL dark-energy expansion law H = H₀·√(Ω(1 + z)³ + (1 − Ω)(1 + z)^(3(1 + w₀ + wₐ))·exp(−3wₐz/(1 + z))) with Ω = `Ω`, w₀ = `w₀`, wₐ = `wₐ`, on some neighbourhood of the time `0`, where H₀ = H(`0`) > 0 and a is positive and differentiable on that neighbourhood) and (`ContDiffAt ℝ 5 a 0`)

Program definitions in this claim:

- `IsFlatCPL Ω w₀ wₐ a t₀` — **PINNED** (pin theorem `flatCPL_pins`): the scale factor `a` obeys the flat matter + CPL dark-energy expansion law H = H₀·√(Ω(1 + z)³ + (1 − Ω)(1 + z)^(3(1 + w₀ + wₐ))·exp(−3wₐz/(1 + z))) with Ω = `Ω`, w₀ = `w₀`, wₐ = `wₐ`, on some neighbourhood of the time `t₀`, where H₀ = H(`t₀`) > 0 and a is positive and differentiable on that neighbourhood

## Author's paraphrase (hand-written; checked only by prose rules)

**Flat matter + CPL models exist for every Ω, w₀, wₐ** (at `t₀ = 0`, `C⁵` there).

## Formal statement (Lean 4)

```lean
theorem exists_flatCPL (Ω w₀ wₐ : ℝ) :
    ∃ a : ℝ → ℝ, IsFlatCPL Ω w₀ wₐ a 0 ∧ ContDiffAt ℝ 5 a 0 := …
```

## Definitions it uses

See GLOSSARY.md: `Cosmography.CPL.IsFlatCPL`, `Cosmography.hubble`, `Cosmography.redshift`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: IsFlatCPL.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): —.
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): unconditional.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): IsFlatCPL: t₀ = 0.
- Source file: `Checked/Cosmography/CPLExistence.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 32
