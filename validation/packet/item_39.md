# Item 39

**Area:** Rigorous simulation of a reaction network

**Source:** see the claim

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**For every** `s : ℝ → ℝ`, `e : ℝ → ℝ`, `c : ℝ → ℝ`, `p : ℝ → ℝ`:

**assuming**

1. the functions `s`, `e`, `c`, `p` (concentrations [S], [E], [C], [P]) solve the mass-action rate equations of E + S ⇌ C → E + P with rate constants k₁ = `1`, k₋₁ = `1`, k₂ = `1` on the time interval [0, `13 / 5`] (derivatives taken within [0, `13 / 5`]), with initial values [S] = `1`, [E] = `1`, [C] = `0`, [P] = `0` at time 0

**then**

1. for every `t : ℝ`, if `t ∈ Set.Icc 0 (25665 / 10000)`, then `p t < 1 / 2`
2. `1 / 2 < p (25666 / 10000)`

Program definitions in this claim:

- `IsMMSolution k₁ km₁ k₂ s₀ e₀ c₀ p₀ T s e c p` — **PINNED** (pin theorem `mmSpec_pins`): the functions `s`, `e`, `c`, `p` (concentrations [S], [E], [C], [P]) solve the mass-action rate equations of E + S ⇌ C → E + P with rate constants k₁ = `k₁`, k₋₁ = `km₁`, k₂ = `k₂` on the time interval [0, `T`] (derivatives taken within [0, `T`]), with initial values [S] = `s₀`, [E] = `e₀`, [C] = `c₀`, [P] = `p₀` at time 0

## Author's paraphrase (hand-written; checked only by prose rules)

Certified half-conversion time of the full Michaelis–Menten mechanism with
k₁ = k₋₁ = k₂ = 1, [S]₀ = [E]₀ = 1, [C]₀ = [P]₀ = 0: every solution of the mass-action rate
equations on the time interval [0, 13/5] (derivatives within the interval) has product
concentration strictly below 1/2 at all times in [0, 2.5665] and strictly above 1/2 at time
2.5666, so half of the substrate is first converted to product between 2.5665 and 2.5666.

## Formal statement (Lean 4)

```lean
theorem mm_half_conversion {s e c p : ℝ → ℝ} (h : IsMMSolution 1 1 1 1 1 0 0 (13 / 5) s e c p) :
    (∀ t ∈ Icc (0 : ℝ) (25665 / 10000), p t < 1 / 2) ∧ 1 / 2 < p (25666 / 10000) := …
```

## Definitions it uses

See GLOSSARY.md: `Sim.MichaelisMenten.IsMMSolution`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: IsMMSolution.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): —.
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): `mm_half_conversion`.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): IsMMSolution: k₁ = 1, km₁ = 1, k₂ = 1, s₀ = 1, e₀ = 1, c₀ = 0, p₀ = 0, T = 13/5.
- Source file: `Checked/Sim/MichaelisMenten.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 39
