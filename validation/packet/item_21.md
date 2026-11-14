# Item 21

**Area:** T1 fidelity

**Source (hand-written: the author's title of the finding or a fixed source line; no check reads it):** standard FLRW cosmology definitions (e.g. Weinberg, Cosmology, 2008; Hogg 1999, astro-ph/9905116); the specification each definition is pinned by is in the statement

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**For every** `Ω : ℝ`, `a : ℝ → ℝ`, `F : ℝ → ℝ`, `t₀ : ℝ`, `t : ℝ`:

**then**

- (the metric F(R) gravity second equation with dust holds with the present matter density parameter `Ω`, the scale factor `a`, the gravity Lagrangian function of Ricci scalar `F`, the present time `t₀` and the time of evaluation `t` (negative Ricci scalar convention, minus the common one; Hubble rate derivative equation of metric F of R gravity; flat FLRW with dust source and kappa squared is one; negative Ricci scalar convention with R taken as curv of `a`; multiplied through by minus two `F` prime with no division)) if and only if (`FRSecondEq Ω a F t₀ t (curv a)`)

Program definitions in this claim:

- `DustDensity Ω a t₀ t` — SPEC, not pinned, so only the formula shown is checked, not its name (for `Ω : ℝ`, `a : ℝ → ℝ`, `t₀ : ℝ`, `t : ℝ`): is defined as `3 * (deriv a t₀ / a t₀) ^ 2 * Ω * (a t₀ / a t) ^ 3`
- `FRSecondEq Ω a F t₀ t R` — SPEC, not pinned, so only the formula shown is checked, not its name (for `Ω : ℝ`, `a : ℝ → ℝ`, `F : ℝ → ℝ`, `t₀ : ℝ`, `t : ℝ`, `R : ℝ → ℝ`): means `-2 * deriv F (R t) * deriv (fun s => deriv a s / a s) t = DustDensity Ω a t₀ t + deriv^[3] F (R t) * deriv R t ^ 2 + deriv^[2] F (R t) * deriv^[2] R t - deriv a t / a t * deriv^[2] F (R t) * deriv R t`
- `MasterEq Ω a F t₀ t` — **PINNED** (pin theorem `masterEq_iff_blind`): phrase (hand-written, linted): the metric F(R) gravity second equation with dust holds with the present matter density parameter `Ω`, the scale factor `a`, the gravity Lagrangian function of Ricci scalar `F`, the present time `t₀` and the time of evaluation `t` (negative Ricci scalar convention, minus the common one; Hubble rate derivative equation of metric F of R gravity; flat FLRW with dust source and kappa squared is one; negative Ricci scalar convention with R taken as curv of `a`; multiplied through by minus two `F` prime with no division); by definition, means `-2 * deriv F (curv a t) * deriv (hubble a) t = Checked.Cosmography.FRCosmo.rhoM Ω a t₀ t + deriv^[2] (curv a) t * deriv^[2] F (curv a t) + deriv (curv a) t * (deriv (curv a) t * deriv^[3] F (curv a t) - hubble a t * deriv^[2] F (curv a t))`
- `curv a t` — **PINNED** (pin theorem `ricciSpec_pins`): phrase (hand-written, linted): the Ricci scalar of flat FLRW with the scale factor `a` and the cosmic time of evaluation `t` (negative convention, de Sitter has negative Ricci scalar; Ricci scalar of a spatially flat FLRW metric; negative convention so de Sitter has minus twelve times Hubble rate squared); by definition, `curv a t` is `-6 * (deriv (hubble a) t + 2 * hubble a t ^ 2)`. Phrase lines proved in Lean (statements in PHRASE_LINES.md): «negative convention, de Sitter has negative Ricci scalar» only assuming `c ≠ 0`; `H ≠ 0`, «negative convention so de Sitter has minus twelve times Hubble rate squared» only assuming `c ≠ 0`

## Author's paraphrase (hand-written; checked only by prose rules)

The program's master equation is the blind `Ḣ` equation with `R = curv a`.

## Formal statement (Lean 4)

```lean
theorem masterEq_iff_blind (Ω : ℝ) (a F : ℝ → ℝ) (t₀ t : ℝ) :
    MasterEq Ω a F t₀ t ↔ FRSecondEq Ω a F t₀ t (curv a) := …
```

## Definitions it uses

See GLOSSARY.md: `Cosmography.FRCosmo.MasterEq`, `Cosmography.FRCosmo.curv`, `Cosmography.FRCosmo.rhoM`, `Cosmography.hubble`, `Fidelity.DustDensity`, `Fidelity.FRSecondEq`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: MasterEq, curv.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): —.
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): `masterEq_iff_blind`.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): —.
- Source file: `Checked/Fidelity/FRSpecs.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 21
