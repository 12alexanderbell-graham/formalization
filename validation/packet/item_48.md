# Item 48

**Area:** F6

**Source:** Bamba, Capozziello, Nojiri, Odintsov, Astrophys. Space Sci. 342, 155 (2012), arXiv:1205.3421 (v1–v3), Eqs. (10.55)–(10.57), copied verbatim from Capozziello & Salzano, Adv. Astron. 2009, 217420, arXiv:0902.0088, Eqs. (56)–(58): curvature terms of the y-redshift d_L coefficients D³_{L,y}, D⁴_{L,y} wrong

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**For every** `K : ℝ`:

**then**

- `(fun x => transverse K x - (x - K * x ^ 3 / 6 + K ^ 2 * x ^ 5 / 120)) =o[nhds 0] fun x => x ^ 5`

Program definitions in this claim:

- `transverse K χ` — **PINNED** (pin theorem `transverseSpec_pins`): the transverse factor S_K(χ) at K = `K`, χ = `χ`: sin(√K·χ)/√K if K > 0, χ if K = 0, sinh(√(−K)·χ)/√(−K) if K < 0

## Author's paraphrase (hand-written; checked only by prose rules)

`S_K(χ) = χ − Kχ³/6 + K²χ⁵/120 + o(χ⁵)` for every `K`.

## Formal statement (Lean 4)

```lean
theorem transverse_expansion (K : ℝ) :
    (fun x => transverse K x - (x - K * x ^ 3 / 6 + K ^ 2 * x ^ 5 / 120)) =o[𝓝 0]
      fun x => x ^ 5 := …
```

## Definitions it uses

See GLOSSARY.md: `Cosmography.Transverse.transverse`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: transverse.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): —.
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): unconditional.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): —.
- Source file: `Checked/Cosmography/Transverse.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 48
