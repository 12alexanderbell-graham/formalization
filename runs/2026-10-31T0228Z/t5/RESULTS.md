# T5 results, judge v5 (run 2026-10-31T0228Z)

Judge: `judge_v5.sh` = the CI checks on main at the base commit (Checked + Work build, forbidden tokens, trust step after author relock, certified numbers, frozen and certified-number diffs vs base). Ports (`ports/`) re-apply a 0028Z/D defect to the tagged records. `final_*` = judged at the last check version (a7f5b6a).

| Defect | Category | Base | Verdict | Caught by / note |
|---|---|---|---|---|
| Ad01 | mistranscription | f367ffb | REJECTED | relock |
| Ad03 | misleading-record | 283f8e9 | ACCEPTED |  |
| Ad04 | wrong-definition | 283f8e9 | ACCEPTED* | only the stale map failed; the author regenerates it (judge fixed later) |
| Ad05 | weakened-statement | 283f8e9 | ACCEPTED* | only the stale map failed; the author regenerates it (judge fixed later) |
| Ad06 | wrong-number | 283f8e9 | REJECTED | numbers, relock |
| Ad07 | unregistered-or-misregistered | 283f8e9 | REJECTED | trust |
| Bd04 | wrong-definition | 283f8e9 | ACCEPTED* | only the stale map failed; the author regenerates it (judge fixed later) |
| Bd05 | misleading-record | 283f8e9 | REJECTED | map |
| Bd07 | wrong-number | 283f8e9 | REJECTED | numbers, relock |
| Bd07s | wrong-number | 283f8e9 | REJECTED | relock |
| Cd02 | wrong-definition | 283f8e9 | REJECTED | trust |
| Cd05 | misleading-record | 283f8e9 | REJECTED | trust |
| Cd06 | weakened-statement | 283f8e9 | ACCEPTED |  |
| Dd01 | misleading-record | 283f8e9 | ACCEPTED |  |
| Dd02 | wrong-number | 283f8e9 | ACCEPTED |  |
| Dd03 | wrong-number | 283f8e9 | REJECTED | numbers, relock |
| Dd04 | mistranscription | 283f8e9 | ACCEPTED |  |
| Dd05 | misleading-record | 283f8e9 | REJECTED | trust, numbers |
| Dd06 | wrong-number | 283f8e9 | REJECTED | numbers |
| Dd07 | wrong-number | 283f8e9 | REJECTED | numbers, relock |
| Dd08 | misleading-record | 283f8e9 | REJECTED | trust |
| final_Ad04 | wrong-definition | a7f5b6a | ACCEPTED |  |
| final_Ad05 | weakened-statement | a7f5b6a | ACCEPTED |  |
| final_Bd04 | wrong-definition | a7f5b6a | ACCEPTED |  |
| final_Cd06 | weakened-statement | a7f5b6a | REJECTED | trust |
| final_Dd02 | wrong-number | a7f5b6a | REJECTED | numbers, relock |
| final_control | control | a7f5b6a | ACCEPTED |  |

## Reading the table
- **Final version (a7f5b6a), judged:** control passes (no false rejection); D02 (input changed beside certified numbers) caught; C06 (bundled conjunction) caught by the trust step (the judge's error filter did not print the line; the only change between its 283f8e9 acceptance and this rejection that touches it is the conjunction rule); A04, A05, B04 still ACCEPTED (the author regenerates the map).
- **Accepted at the end of the run (open):** A03 (scope prose), A04, B04 (new wrong definitions labelled FORMULA/COMPOSITE), A05 (existential headline), D01 (certified values with swapped prose labels), D04 (record of a free formula, misleading docstring). Six of the 20 distinct defects judged this run (A01, A03–A07, B04, B05, B07 with variant B07s, C02, C05, C06, D01–D08), all six in the class "meaning carried by prose or names".
- **Caught:** every wrong-number defect (A06, B07, B07s, D02, D03, D07), every changed frozen item (A01), unregistered/invented citations (A07, C05, D08), D05 (¬RoundsTo), D06 (section scope), C02 (decorative spec), B05 (hand-edited map), C06.
- Not re-judged under v5 (caught under v3/v4 in run 0028Z, v5 only adds checks): A02, A08r, B01–B03, B06, B08, C01, C03, C04, C07, C08.
