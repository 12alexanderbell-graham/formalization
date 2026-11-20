# Run 2026-11-20T0228Z

**THE RESULT:** part 3 by rotation (STATE 2f → part 3 as in section Next of `runs/2026-11-19T2028Z/README.md`, trust track T5). Reader test EP2 decided rule M10; a held-out red team against M9 was run (section What we did).

**What can a scientist now trust without checking it themselves, that they could not before?** A hand-written line that compares a statement with a model's name used as the reference ('to Gelfand', 'of Falkner–Skan') can no longer sit next to a listed statement in the records; it left a false fidelity doubt in 5 of 6 blind readers.

**Weakest unchecked step:** plain false descriptions of a statement in vocabulary words still pass every rule (20 such lines from red team M9h); readers have refuted this kind from the generated statement (1 doubt in 9 readers over three tests), but no rule reads them. The judge's slowest job is still nanoda shard 1 (section Next).

## Start
- 02:28Z. Local main was a stale divergent clone (fa47717 of wip/leanchecker-shards); `git checkout -B main origin/main` at 0792b21. No LOCK → taken (b0af37a).
- CI at start: 44655372746 (0792b21, two new Trust modules) running; read in section CI read.
- Local Lean: elan + Mathlib cache ≈ 3 min; `checked-build` of 44640560624 (d363b3d) restored with FORCE=1 DELETE_ZIP=1 (`~/.cache/mathlib` deleted first; 2.8 GB free after); `lake build Checked` replayed it and built the two new Trust modules (3720 jobs, under 2 min).

## Bottleneck (and what a yes/no changes)
- Part 3 (rotation): the LEDGER experiment of run 2028Z — is a model eponym used as the reference ('to Gelfand') harmful to readers at six readers (test EF: 1 of 3, one short of its threshold)? Yes → rule M10 closes the last measured reference shape that passes; no → recorded harmless at that dose. And: does M9 catch reference lines written blind to it (held-out red team)?

## What we did
- **Brief first** (`t5/BRIEF_EP2_M9h.md`, committed 548ea21 with the page builder `t5/make_pages_EP2.py`, before any reader or red team ran): arms, keys (test EF's), decision rules for both measurements.
- **Reader test EP2**: nine blind Sonnet readers in one message with the red team (EP: six readers, test EF's eponym lines verbatim; N: a fresh baseline of three, test LN's lines), each on STATE.md + CLAIMS_READER.md of 548ea21 with the arm's three lines, the lines describing earlier tests of this shape dropped in every arm; blind grader under shuffled labels. Result (`t5/READERS_EP2.md`): **EP 5/6, N 1/3** with an unrejected fidelity doubt (blind grader; the run's grading EP 5/6, N 0/3, one reader differs); four of the five EP doubts borderline ("the equations look standard to me. I would check the sign conventions against the source before citing"); citation 0/27 misled.
- **Rule M10** of `scripts/trust/check_headline_mentions.py` (by the registered decision rule: EP harmful): on a line about a listed headline, a model eponym of `M10_EPONYMS` (one name or a hyphenated pair) not directly followed by a noun of `M10_NOUNS` names a source for M6, so the line may hold only the citation; 'the Gelfand problem', 'the Bonnor–Ebert mass', 'Falkner–Skan β' pass. Binds from its own commit (`m10_grandfathered`, as M9). Selftest 85 → 92 defects, 7 → 9 correct lines. Cost (`t5/cost_m10.py`): 0 findings on lines written since M9's commit; 156 on all record lines ever written (not re-read).
- **Red team M9h** (held out: at 83df9c6, rules M1–M8, before M9 and before test EF's brief; not shown M9): 21 accepted lines in ≈ 2.5 min (`t5/m9h_lines.txt`; 21/21 pass at the target, 7 flagged on main). Class A by the brief (a pointer at a reference the reader cannot see): 1 line ('the Hartree normalisation of the exponent'), flagged → EFFECTIVE on 1 of 1 by the registered rule, a sample that measures nothing (inconclusive). The other 20 are plain false descriptions of what a statement says, in vocabulary words ('the ball is of dimension two', 'the parameter is the square of the sup norm'): no reference, the arm-N shape. Root cause of the empty sample: the brief did not exclude such lines, and almost every reference word already fails M1 or M6. Fixed for the next held-out red team (PROMPT note; LEDGER experiment).

## Measure
- T5: test EP2, 9 readers: model eponym as the reference 5/6 harmful → closed by M10; red-team reference shapes known to pass every rule: one fewer (the eponym shape recorded as a limit by red team M6r and test EF). Red team M9h: M9 1/1 on class A (inconclusive); 20 plain false descriptions pass every rule (recorded limit).
- Pooled with test EF (record only): eponym arm 6/9; no-reference arms 1/9 over tests LN, EF, EP2.

## CI read
- 44655372746 (0792b21, run 0028Z's two new Trust modules; no headline changed) concluded green on every job at 03:17Z: checked job, work job, leanchecker 4/4, nanoda 4/4 → nothing to promote; its necessity theorems are judged.
- Judge times of 44655372746 (job start to end of the check step): leanchecker replay steps 36, 64, 65, 67 min (shards 0–3); nanoda steps 30, 64, 42, 32 min. Nanoda shard 1: 77,824 of 336,358 constants, 236,131 declarations with dependencies, export 56.4 M lines (243 s), check 3582 s on 4 workers; nanoda shard 0: 78,931 constants, 222,336 declarations, 44.9 M lines (201 s), check 1569 s. Same constant count, 2.3× the check time: a few heavy declarations, not the shard's size, make shard 1 slow. The leanchecker shards, balanced on leanchecker times of 2026-11-19, are now 1.8× apart (shard 0 light).

## End
- Local before the final push: `lake build Checked` (3720 jobs), StatementDeps without relock (302 headlines, NV 182/182; NEEDED 740, REDUNDANT 218, open 61; TRUST_MAP unchanged), Claims (302 generated claims; CLAIMS.md unchanged), check_headline_mentions selftest (92 defects, 9 correct lines) and `--base` d363b3d and 0792b21, goal guard, check_status_lines, precheck_citations, records_check.py (see the final commit message).

## Next
- CI read first: the run of this run's final push (M10 in the checked job's records step; no Lean change, so the kernel jobs should report memoised passes).
- The judge: leanchecker shards 1–3 (64–67 min) and nanoda shard 1 (64 min) bound every promotion; shard 0 of both is light (30–36 min). (1) Refresh `scripts/nanoda/shard_times.txt` from the `leanchecker-time` lines of 44655372746's four leanchecker logs (`runs/2026-11-19T0628Z/scripts/times_from_logs2.py`) and regenerate the assignment; (2) nanoda needs its own times: nanoda shard 1's slowness is not its size (same constant count as shard 0), so find its heavy declarations (export one module group at a time with `exportshard` and time nanoda on each) before giving nanoda its own assignment.
- Then by rotation (part 3 at 0228Z, part 1 at 0028Z, parts 2/5 at 2228Z): parts 2/5 as in section Next of `runs/2026-11-19T2228Z/README.md`; part 1 as in section Next of `runs/2026-11-20T0028Z/README.md`. Part 3 later: the held-out red team against M10 (LEDGER experiment of this run; brief excludes lines with no pointer at a reference); then the plain false descriptions of a statement (20 shapes from M9h): measured harmless so far (arm N, 1 of 9 readers), so a reader test at a higher dose before any rule.
