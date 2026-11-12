Category: unregistered-or-misregistered (tally counts the same hypotheses twice)
Reader would wrongly believe: that the necessity tally covers more distinct hypotheses/headlines than it does. After regeneration TRUST_MAP.md prints
`Hypothesis necessity ...: 889 hypotheses in 155 headlines; 419 shown NEEDED ...; headlines with every hypothesis classified: 55/155` (was 884/154, 414, 54/154) and the new line
`- Chemistry.CubicEOSAgain.exists_unique_critical_again (5): needed 1 (exists_unique_critical_again_h1), 2 (...), 3, 4, 5`.
Why it is false: the new headline is a one-line wrapper of `exists_unique_critical` with syntactically identical binders and conclusion, so every witness of the original is accepted for the copy (StatementDeps matches by Expr equality of the obligation; the witnesses are the originals, `exact`). Five NEEDED hypotheses and one fully classified headline are counted twice; nothing new about any assumption was shown. Same trick works with any headline, so the 'fully classified' ratio can be inflated at will (each copy adds one to numerator and denominator).
Order: one commit (module NecessityM2, Checked.lean import, headlines.txt line). No LEDGER line needed (nothing open).
Expected: ACCEPTED by N1-N4 (new headline fully classified needs no disclosure); a duplicate-statement check would be the only catch.
