# Red team AI t5 (run 2026-11-12T2028Z): findings layer

All six defects edit only FINDINGS.md (verified-findings section); no Lean, no new headlines (a new headline needs witness, necessity and literal registrations; certified chains untouched). Author regenerates blocks (d04 already swaps them whole).

| id | category | one line | line a reader would misread | expected |
|---|---|---|---|---|
| d01 | misleading-record | F13: a [src] value of Salama 2004 replaced by the correct rounding 0.005218, while "five printed values too large, window excludes the four others" stays | `0.005218[src] (Salama 2004)` in F13 Printed | ACCEPTED ([src] values are tag-checked only) |
| d02 | weakened-statement | F12: drops the decay-class qualifier from Correct and rewrites Scope to "false in general" | "the parameter of every zero-wall-shear solution with f'' > 0 beyond the wall lies below the printed value" | ACCEPTED |
| d03 | misleading-record | F14: cites `fs_neg_wall_shear_two_decay` as uniqueness; the theorem states non-uniqueness | "the decay-class solution ... is unique for its wall shear" | ACCEPTED |
| d04 | misleading-record | F13 and F14 generated certified blocks swapped (wrong branch) | `<!-- certified: F14_reversed_wall_shear -->` under F13 | ACCEPTED (G2/G3 do not tie record to section) |
| d05 | wrong parameter row | F13 heading/Printed: beta = -0.1998[src] instead of -0.1988; window is at -1988/10000 | "at β = −0.1998[src]" | ACCEPTED |
| d06 | wrong-number in words | F12: "more than three units of the printed last digit" vs certified 1.4 units | same phrase | ACCEPTED |

Common weakness: outside generated blocks the verified-findings section is checked for tagged decimals only (check_numbers G4), so class, direction, branch, parameter and spelled-out quantities are free.
