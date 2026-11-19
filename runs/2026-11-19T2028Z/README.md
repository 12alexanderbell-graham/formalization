# Run 2026-11-19T2028Z

**THE RESULT:** part 3 by rotation (STATE 2c → part 3 as in section Next of `runs/2026-11-19T1428Z/README.md`, trust track T5), and a repair of the judge every promotion waits on (integrity event 39.5). Reader test EF decided rule M9; nanoda now checks in parallel behind planted controls (section What we did).

**What can a scientist now trust without checking it themselves, that they could not before?** A hand-written line that compares a statement with an unnamed reference ('the formula') can no longer sit next to a listed statement in the records; it misled 2 of 3 blind readers. And the independent second checker of every statement now runs on every core of its machine, so a new statement is judged in about an hour instead of three.

**Weakest unchecked step:** the remaining prose shapes no reader test has measured (a model eponym as the reference: 1 of 3 readers, one short of the threshold), and the nanoda timing prediction until the first main run with workers ends (section Next).

## Start
- 20:28Z. Local main was a stale divergent clone; `git checkout -B main origin/main` at 7681007. No LOCK → taken (1101a36).
- Local Lean: elan + toolchain ≈ 1 min, `lake exe cache get` ≈ 3 min; `checked-build` of 44598131615 (e42bd17) restored with DELETE_ZIP=1 (2.8 GB free afterwards).
- CI at start: 44577216209 (1b242fe, promotion of `laneEmden52_constants`): checked job, leanchecker 4/4, nanoda shards 0, 2, 3 green; nanoda shard 1 running since 17:41Z. 44598131615 (e42bd17): checked job green at 20:08Z, kernel shards running.

## Bottleneck (and what a yes/no changes)
- The judge: every promotion of the last two days waited three hours or more on nanoda shard 1 (196 min in 44521044439, past 170 min in 44577216209; shards 0, 2, 3: 57–90 min), and run 0228Z's experiment (every nanoda shard under 150 min) was not met. Question: why is one shard so slow when the leanchecker shards are balanced? Yes, a cause the program controls → every later promotion judged hours sooner.
- Part 3 (rotation): the two recorded limits of M8 (section Next of run 1428Z): does a model eponym ('to Gelfand') or a non-document word ('the formula') used as the reference plant a false fidelity doubt the way a named source does (test LN: 3/3)? Yes → a rule; no → recorded as measured harmless.

## What we did
- **Root cause of the slow nanoda shard:** `scripts/nanoda_shard.sh` wrote no `num_threads`, and nanoda_lib then checks every declaration on one worker; the runner has 4 cores and 15 GiB (shard 1 used 1.4 GiB, log of job 135549651562). The shard assignment balances leanchecker's times and cannot fix a single-threaded checker (the four nanoda shards sum to 433 min).
- **Repair** (`scripts/nanoda_shard.sh`, pushed 83df9c6 with CI on purpose): `num_threads` = `nproc` (nanoda_lib's own option at the pinned 8de7e0c; read in `src/tc.rs`: workers take the next declaration index until all are taken; a failed check panics in its worker and `join` re-raises it, exit 101). Before the shard, nanoda runs with the same configuration on the planted exports of `scripts/nanoda/controls/` (`ndctl_good.txt`, lean4export v4.35.0 of five core declarations, must pass; `ndctl_bad.txt`, one literal false, must be rejected), else the job fails; each phase prints `nanoda-time`. Local: the controls behave as required with 1 and 4 workers; the harness fails when the bad control is replaced by the good one; a real export (`Checked.Trust.HzWallS`'s thirteen theorems with dependencies, 20,291 declarations) checks in 34.5 s on one worker and 17.7 s on two.
- **Reader test EF** (`t5/reader_brief_EF.md`, committed 2d485dc before the readers; `t5/make_pages_EF.py`): nine blind Sonnet readers in one message, three arms of three lines each under the same three headings as test LN: N (no reference, LN's lines verbatim), EP (a model eponym: 'to Gelfand', 'of Falkner–Skan'), F ('of the formula'); blind grader under shuffled labels. Result (`t5/READERS_EF.md`): N 0/3, EP 1/3, F 2/3 readers with an unrejected fidelity doubt; both gradings agree on every reader; no citation answer misled (27/27 "yes").
- **Rule M9** of `scripts/trust/check_headline_mentions.py` (by the registered decision rule: F harmful): on a line about a listed headline, a determiner with up to two words before formula, equation, expression, result, version, derivation, definition, notation, specification or glossary names a source for M6, unless a code span follows the noun or the noun is the statement's own ('the equation in the statement'); 'THE RESULT' (the program's plan) is exempt. Selftest: 85 defects (seven M9 lines, the three F lines among them) and 7 correct lines; binds from its own commit (`m9_grandfathered`). Cost (`t5/cost_m9.py`): 0 findings on the lines written since M8's commit; 57 on all record lines ever written (not re-read).

## Measure
- Nanoda: serial check time of the slowest shard 196 min (44521044439); prediction with 4 workers ≈ 55–60 min (local scaling 1.95× on 2 cores). Read on 44611137609 (83df9c6), the first main run with workers (section End).
- T5: test EF, 9 readers, the shape 'the formula' as the reference 2/3 harmful → closed by M9; eponym shape 1/3 → recorded, open. Red-team shapes known to pass every rule: one fewer.

## CI read
- See Start and End.

## End
- 21:04Z. 44577216209 (1b242fe) concluded green on every job (nanoda shard 1: 3 h 24 min on one worker) → `laneEmden52_constants` PROVED: judged template in its STATE.md heading; Alexander told.
- 21:22Z. 44611137609 (83df9c6, the first run with nanoda workers), nanoda shard 0: both planted controls as required in CI (the false export rejected, `panicked at src/tc.rs:985:71`), export 165 s, check 1245 s on 4 workers for 221,912 declarations (the serial step of this shard took 57 min in 44521044439), 1.9 GiB used; passed. Shards 1–3 and the kernel shards still running at the final push.
- Local before the final push: StatementDeps (301 headlines, NV 181/181; no relock, no Lean change), Claims (CLAIMS.md unchanged), check_claims, check_headline_mentions selftest and --base 1b242fe, check_status_lines, goal guard, records_check.py 1b242fe (see the final commit message).

## Next
- CI read first: 44611137609 (83df9c6): nanoda shards 1–3: `grep 'nanoda-time\|nanoda control' <log>` in each; evaluate the LEDGER experiment (every shard's check under 75 min; both controls as required in every shard; no memory failure). Then the run of this run's final push (M9 in the checked job's records step; no Lean change).
- If a nanoda shard stays above 75 min: read its `nanoda-time` lines against the shard's export size and rebalance nanoda on its own times (`nanoda-time check` per shard is now in every log); if leanchecker becomes the slowest job, run two to four of its groups at once in `scripts/leanchecker_shard.py` (memory first: one group's peak RSS).
- Then by rotation (part 3 at 2028Z, part 1 at 1828Z, parts 2/5 at 1628Z): parts 2/5 as in section Next of `runs/2026-11-19T1628Z/README.md`; part 1 as in section Next of `runs/2026-11-19T1828Z/README.md`. Part 3 later: the eponym arm at a higher dose (LEDGER experiment of this run: six readers and a fresh N arm), and a held-out red team against M9 (lines written against the rules of 2d485dc, scored by M9 as committed).
