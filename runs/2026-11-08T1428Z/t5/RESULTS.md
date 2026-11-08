# Blind red team V — results (run 2026-11-08T1428Z)

Brief `briefV.md` committed alone in a470d2e before the red team started; snapshot = d80f565 (branch `wip/findings-gen`: rules G1–G4 on top of R0–R4, S1–S4, P1–P2) with the `.lake` files of the author-files artifact of CI run 42483811134. Red team: Sonnet subagent, FINDINGS.md only, ≈ 2 min. Judge: this session copied each defect's FINDINGS.md into a clean worktree of d80f565 and ran `check_numbers.py`, `check_numbers.py --base d80f565`, `check_prose.py`, `precheck_citations.py` (all exit 0 for all six). Each defect is a one-sentence edit (diffs in `redteamV/dNN/FINDINGS.diff`); all six are valid (each makes a FINDINGS sentence false).

| defect | what the reader is led to believe | adjacent generated block contradicts it? | BLIND (G1–G4) | AFTER (G5, G6; not blind) |
|---|---|---|---|---|
| d01 | `F1_l0` certifies the printed formula's value, `F1_printedL0` the true l₀ (names swapped) | yes (roles in the block) | ACCEPTED | rejected (G6) |
| d02 | the printed CPL l₀ is "too large" (it is too small: `F2_error` is true − printed > 0) | yes (difference(derived−printed) and the order line) | ACCEPTED | ACCEPTED |
| d03 | the F11 size is certified "at q₀ = −1/2" (it is at −0.8) | yes (selector q₀ = −0.8) | ACCEPTED | rejected (G5) |
| d04 | the pole of the printed F(R₀) expression lies at Ω > 1 (it is at ≈ 0.54) | yes (`RoundsTo r …` in the quote) | ACCEPTED | ACCEPTED |
| d05 | the Milne sizes are parts per thousand, the curvature shift per cent (swapped units) | yes (the `100 *` factor) | ACCEPTED | ACCEPTED |
| d06 | the correct η values "agree in sign" with the printed ones at Ω = 0.041 | no (the block lists only correct values; the Printed bullet contradicts it) | ACCEPTED | ACCEPTED |

**Blind: 6/6 valid defects accepted** — but none of them puts a certified number in an author sentence: G1 forced every falsehood into number-free commentary, and in 5/6 the generated block a few lines below states the true value, role, argument or factor. The class round U exploited (author words in the same sentence as a tagged number) has no instance left: any certified tag, bound input or number equal to a certified value outside a block is rejected (G1), and any edit inside a block is rejected (G2).

**After (not blind):** G5 (fractions equal to a certified value; `v = c` next to a record's name must be a value Lean fixes v to) and G6 (the role word nearest before a record's name must be that record's role) reject d03 and d01: 4/6 accepted (d02 direction, d04 range, d05 unit, d06 sign against a quoted number). Those four are statements of commentary about a certified result; closing them by word rules is the deny-list pattern that has not converged since round F, so they are left open and the file says what is checked (G4).

**Diagnosis:** the generated layer (blocks, CLAIMS.md, TRUST_MAP) is now the only place a certified number can stand; what remains attackable in FINDINGS is commentary, which is labelled unchecked. The next measurement target for part 3 is the generated layer itself and the kernel statements behind it (a red team that must change what a block or CLAIMS.md says), not more commentary rounds; and the commentary sentences that carry a result (direction, range, unit, sign) can be generated from the records the same way (STATE next step).
