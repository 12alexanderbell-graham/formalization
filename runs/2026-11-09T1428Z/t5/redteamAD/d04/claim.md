# d04 – exclusions are keyed by (definition, text): the same hypothesis lines for the sibling definitions

Weakness: P9/P12 granularity. The first clause reader gave `lumDist` and `angDist` the lines "emission time is not later
than observation time" and "requires a positive continuous scale factor between emission and observation" (hypotheses of
their pinning theorems, excluded in `phrase_clause_baseline.txt` as domain remarks that read as constraints the total
Lean definition does not have). `lumDistFlat` and `comoving` are pinned by `lumDistFlat_pins`/`comoving_pins` under exactly
the same three hypotheses (FlatPins.lean) and the first reader wrote nothing for them. A blind reader of those two writes
the same sentences; they are not excluded under the new keys, P9 forces them in.

Generated phrases:

> lumDistFlat: (units in which the speed of light is one; **emission time is not later than observation time; requires a
> positive continuous scale factor between emission and observation**)
> comoving: (integral of one over the scale factor over cosmic time; integrated from emission time to observation time;
> units in which the speed of light is one; **emission time is not later than observation time; requires a positive
> continuous scale factor between emission and observation**)

Overstated against the bodies `lumDistFlat = a t₀ * (1 + redshift a t₀ t) * comoving a t₀ t` and
`comoving = ∫ s in t..t₀, 1 / a s`: both are total definitions (a signed integral for t > t₀; Lean junk values for a ≤ 0);
the phrase presents the hypotheses of a pin theorem as part of what the quantity is. Weak-to-medium severity (the body
shows no condition, but "requires" is a hypothesis list); a reader may judge it DISCLOSED.

Rules passed: as d02 (0 problems from `_controls`, `coverage`, `registry_complete`, `generated`, `baseline_reentry`,
`registry_removals`, growth, LEDGER). Route: four added registry lines. Survives P10/P11 as implemented.
