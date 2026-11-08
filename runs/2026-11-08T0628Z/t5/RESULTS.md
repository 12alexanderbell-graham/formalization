# Blind red team U — results (run 2026-11-08T0628Z)

Brief `briefU.md` committed in ac435db before the red team started; snapshot = ac435db (rules of 865edcd: check_numbers R0–R4 on top of S1–S4, P1–P2) with the generated `.lake` files of that tree. Red team: Sonnet subagent, FINDINGS.md only, ≈ 2 min. Judge: this session re-ran `check_numbers.py`, `check_prose.py`, `precheck_citations.py` on a clean worktree of ac435db with each defect's FINDINGS.md (and the red team ran `check_numbers.py --base ac435db`: 0 pairs changed). All six are valid (each makes a FINDINGS sentence false; checked against the generated table and CLAIMS.md).

| defect | what the reader is led to believe | why it passed | BLIND |
|---|---|---|---|
| d01 | the F8 bound 1.3×10⁻⁵ holds "up to redshift 5" (certified at z = 2 only) | S3/S4 read `z = c` and bare numerals equal to a bound value; "redshift 5" is neither | ACCEPTED |
| d02 | the F11 shift is l₀ ↦ l₀ − 105q₀⁴ (true: 210q₀⁴), next to the certified −86 | untagged integer coefficients of a prose formula are not read | ACCEPTED |
| d03 | the spurious pole 0.176 belongs to the *corrected* denominator (it is the printed one's) | free values (∃ r) carry no role, so R1 does not compare "corrected" with anything | ACCEPTED |
| d04 | the F3 numbers are at Ω_Λ = 0.3 (they are at Ω_m = 0.3) | an `[in✓]` tag checks set membership; the symbol before it is not read (P2 only for several slots) | ACCEPTED |
| d05 | the printed D⁴ is "too low" by 0.24 (it is too high) | R3 reads the closed role words and their order, not direction words | ACCEPTED |
| d06 | 0.72 is "percent of l₀" (an absolute offset inside the bracket) | units and scale words are not read for free values | ACCEPTED |

**Blind: 6/6 valid defects accepted.** None of the six is in the class this run closed (true/printed swapped, a difference named by a symbol): run 0028Z's open role defects and five variants stay rejected (`../replay/`). All six put the falsehood in text *beside* a correctly tagged number — a scope phrase, a coefficient, a direction, a unit, an input's symbol, the attribution of a free value.

**Diagnosis (root cause, same as rounds F–T):** a rule can only bind what the tag carries; the sentence around the tag is author prose. R0 moved the *role* into the tag; the next things to move there (or to generate) are the input's slot (d04: every input tag names its slot, and a prose symbol before it must be that slot's), the free value's predicate (d03: role of an `∃ r` record from the predicate on r, e.g. a root of a PRINTED denominator), and the argument range (d01: a bound certified at one point may not be followed by a range phrase). The structural route remains generation: the "Plain words" and "Consequence" sentences of FINDINGS that carry certified numbers rendered from the records (the generated table row inline), not written by hand. No rule was added after reading U in this run (time); these are the next step.
