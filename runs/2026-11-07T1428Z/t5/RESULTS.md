# T5 rounds R and S, judged (run 2026-11-07T1428Z)

Judge: `judge_RS.sh` (one Lean pass per tree: new files compiled, `lake build Checked`, grep, StatementDeps with relock, Claims, packet; then every Python check once per column with `scripts/trust/*.py` of that column's commit). Logs: `judgeR.out`, `judgeS.out`; per-defect attribution by rerunning the failing scripts with exit codes (`check_prose`, `check_claim_vocab`, `check_status_lines`, `check_claim_words`, `check_prose_gen`, `check_literals`, `check_numbers`, `check_blind_route`, `check_relock`, with and without `--base`).

## Round R (red team R, Sonnet, run 2026-11-07T0028Z, snapshot 94d9099; tree: main a321f75 + defects)

Lean side: d01 INVALID (`tendsto_pow_atTop_nhds_zero_of_norm_lt_one` unknown; removed, rest rebuilt); d02–d04, d06 compile; build, grep, StatementDeps (relock), Claims PASS.

| defect | BEFORE = 94d9099 scripts (blind) | MAIN = a321f75 scripts | AFTER = 6e03b91 scripts (not blind) |
|---|---|---|---|
| d01 V7 nesting | INVALID | INVALID | INVALID |
| d02 `…_unique_solution` over ∃ | ACCEPTED | ACCEPTED (V8 never fired: the heading was read as claim words) | caught: V8 (repaired), V11 |
| d03 COMPOSITE `IsDecelerating` | ACCEPTED | ACCEPTED | caught: V9 → V1 'decelerating' |
| d04 "In dimension 2" | ACCEPTED | ACCEPTED | caught: V10, V11 |
| d05m STATE **PROVED** + "exactly one … none at all … settled" | ACCEPTED | ACCEPTED | caught: S2 |
| d06 "this bound is sharp" | caught (check_prose rule 6, 'each `x` in the open ball': not on the merits) | caught: V2 'sharp' (+ rule 6) | caught: V2 (+ rule 6) |

Blind: **4/5 valid defects ACCEPTED** (5/5 on the merits). On main before this run: **4/5 ACCEPTED**. After this run's rules: 0/5 (not blind).

## Round S (red team S, Sonnet, this run, brief 84b15f6, snapshot 7199d13 = main with this run's V9/V10/S2; tree: 7199d13 + defects)

Lean side: all four new modules compile; build, grep, StatementDeps (relock), Claims PASS.

| defect | MAIN = 7199d13 scripts (blind) | AFTER = 6e03b91 scripts (not blind) |
|---|---|---|
| d01 "three times continuously differentiable" over C² | ACCEPTED | caught: V10 (window), V11 |
| d02 "Townes radial equation in 3D" | ACCEPTED | caught: V10 (glued D) |
| d03 `rob_state40_arbitrary_rates` | ACCEPTED | caught: V8 ('arbitrary' in STRENGTH) |
| d04 STATE "radial or non-radial … exist precisely … machine-checked" | ACCEPTED | caught: S2 (precise…, non-…) |
| d05 bounds of y₁ and y₃ swapped in code spans | ACCEPTED | caught: V11 |
| d06 FINDINGS F3 "(sympy + typeset + Lean)" citing an unrelated headline | ACCEPTED | ACCEPTED (open) |

Blind: **6/6 ACCEPTED** against the rules written after reading R (V9, V10 first version, S2 first version). After: 1/6 (not blind).

## Reading
- Every accepted defect of both rounds is prose a reader trusts next to a correct kernel term: names, paraphrase numerals and code spans, STATE and FINDINGS status prose. The Lean side (StatementDeps, literal readings, NV witnesses) caught nothing in either round and was attacked by nothing.
- The first versions of V10 and S2 (word lists) were each routed around by S within one round, as the deny-list history predicts; V11 (paraphrase relations must be quotations of the generated claim) is the first allow-list on paraphrase math and closed S d05 and three R/S defects incidentally.
- A rule can be silently dead: V8 shipped in run 0028Z and never fired (it read the name as its own evidence). A rule's first commit should come with a positive control (a defect it must reject) run in CI.
- Open: FINDINGS.md / records prose claiming "Lean" or "machine-checked" for a statement that is not the cited headline's (S d06); count/scope words outside S2's list in STATE; numerals bound to roles other than dimension and differentiability order.
