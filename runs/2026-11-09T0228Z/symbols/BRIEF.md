# Brief: blind reader of the cosmographic letter names (run 2026-11-09T0228Z)

**Purpose.** Under rule P7 (stated in `runs/2026-11-09T0228Z/clauses/BRIEF.md`) every word of the plain-words phrase
of a pinned definition must come from a blind reader. The definition `Checked.Cosmography.Aviles.cosmoCoeff n a t`
(binders: `n` the derivative order of the coefficient, `a` the scale factor, `t` the time of evaluation) is the
dimensionless cosmographic coefficient of order `n`. Scientists name these coefficients by conventional letters.
Your answer will be compared mechanically with what other texts of the program use; be exact and plain.

## What you may read
- The Lean source of `cosmoCoeff` (find it with grep under `Checked/`; its signature and body only, not its docstring)
  and the specification `Checked/Fidelity/RedshiftCoeffSpecs.lean` (structure `CosmoCoeffSpecCore`, theorem
  `cosmoCoeffCore_pins`).
- Your own knowledge of the standard cosmography literature (the conventional names and letters of the coefficients).

## What you must NOT read
`scripts/`, every `*.md` file other than this brief, `validation/`, `runs/` (except this folder), `Work/`, `_archive/`,
`Checked/Records/`, the git history, the web.

## Output (write exactly one file: `runs/2026-11-09T0228Z/symbols/SYMBOLS.txt`)
For each derivative order from 2 up to the highest order you can name with confidence, one line:

    CLAUSE | Checked.Cosmography.Aviles.cosmoCoeff | <clause>

where `<clause>` says, in plain English (3 to 14 words, no formula characters, no comma or semicolon), how the order
`k` coefficient of this definition relates to the conventionally named cosmographic parameter and its usual letter
(say "minus" if a sign differs; check signs against the Lean body). Then one line that lists the letters of the
orders you named in increasing order, in the form

    CLAUSE | Checked.Cosmography.Aviles.cosmoCoeff | <letters separated by spaces> for the orders <orders separated by spaces>

Then `END` and a short note on anything uncertain.
