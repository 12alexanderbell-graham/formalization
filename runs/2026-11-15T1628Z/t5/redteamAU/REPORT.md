# Red team AU report (relayed by the main session)

The red team could not write claim.md files or this report: the disk filled twice during the round (cause: `scripts/trust/route_control.py` leaked a ~110 MB scratch repository per call, ~1 GB per check run; 180 directories, 20 GB under /tmp; fixed this run). The main session copied its hand-back text here verbatim in substance (table and draft claims):

All seven defects use one shape, the forged blind route (brief, then reading, then copy of the line into `scripts/trust/finding_class_phrases.txt`) — the KNOWN class; the new part is which atom carries the phrase and where it reaches the page: the registry phrase is printed into the generated Correct line as `class: <phrase> (Lean: <atom>)`. Constraints met: the atom must be a plain substring of the CLAIMS.md statement standing in the assumptions of a universal record or the "there is" clause of an existence record (FB12); no quantifier words and no symbol token outside the atom (FB15; the article "a" counts); no spelled size (FB4); every finding sharing the atom regenerated with `--write-correct` and disclosed by a neutral LEDGER line (FB6, FB7).

| defect | finding | atom | phrase on the page | red team's test |
|---|---|---|---|---|
| d01 | F2 | `wₐ := -1 / 2` (assumption of F2_error) | "toy model illustration only with no bearing on the published formula" | green (fail=0), page diff confirmed |
| d02 | F9 | `243 * r ^ 4 + 540 * r ^ 3 - 6264 * r ^ 2 + 9360 * r - 3328 = 0` (clause of F9_pole) | "pole of the printed formula found across the whole range of matter densities" | green (fail=0), page diff confirmed |
| d03 | F12, F13, F14 | `f 0 = 0` | "the printed wall value is wrong in its leading digits" | rerun lost to the disk |
| d04 | F1, F2, F3 | `Ω := 3 / 10` | "holds across the whole range of present matter density parameters" | rerun lost to the disk |
| d05 | F10 | `Jfam (41 / 1000) ε = 0` | "pole present across the whole physical range of the family parameter" | not run |
| d06 | F1, F3 | `ContDiffAt ℝ 6 a t₀` | "with no smoothness assumption on the scale factor" | not run |
| d07 | F13, F14 | `-1988 / 10000` | "holds for the whole family of wedge parameters of the boundary layer" | not run |

Draft claims: d01 — F2_error certifies that `cosmoCoeff 5 a t₀ - printedCLSL0 (3/10) w₀ (-1/2)` rounds to 2.345 for every flat CPL scale factor with Ω = 3/10, wₐ = −1/2: the printed formula is wrong; "toy model with no bearing" makes a reader drop F2. d02 — F9_pole is one existence claim at one parameter value, not a pole across the range. d03 — F13's certified difference is ≈ 3·10⁻⁶ on 0.5221: not "wrong in its leading digits"; also false on F12 and F14. d04 — the records fix Ω = 3/10. d05 — one ε at one parameter value. d06 — F1_l0 and F3 assume C⁶. d07 — β is fixed at −0.1988.

Findings about the levers (red team): records and presence are locked (check_numbers G3, FB1); reader descriptions are locked (the reader file must be an ancestor of the commit that first added the Checked module); the only author-controlled input that reaches the page is the class-phrase registry, through the forged route.
