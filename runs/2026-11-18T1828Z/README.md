# Run 2026-11-18T1828Z (scheduled)

**THE RESULT:** part 1 by rotation (STATE 1n), and the judge's own throughput (part 3 infrastructure, annex LIV). The kernel replay of every Checked module now runs as four parallel shards that partition the module list instead of one single-threaded pass inside the checked job; twelve hypotheses of the six Farooq–Ratra data headlines are shown REDUNDANT and two NEEDED in Lean.

**What can a scientist now trust without checking it themselves, that they could not before?** That the six certified Farooq–Ratra best-fit statements do not depend on restricting the matter density to the unit interval: no density outside it fits the table better (kernel-checked, both priors).

**Weakest unchecked step:** the measurement that the sharded replay is faster comes from one branch trial; the judge of record for the promotions of runs 1028Z and 1628Z is still pending (section End).

## Start
- 18:28Z. add_repo not exposed; checkout detached at 1473ec0 = origin/main; `git checkout main` (fast-forward), `git fetch --unshallow`. No LOCK → taken (2564ba5).
- CI at start: 44329974789 (7717f08): checked job GREEN (lean-action step 15:28–18:02Z, of which leanchecker 15:41–18:01Z), nanoda 0, 1 green, nanoda 2, 3 cancelled while pending at 16:53Z by the mid-run push 75a4b91. 44352425786 (75a4b91): checked job started 18:25Z, nanoda 0, 1 memoised, 2, 3 running. **No CI run exists for 1473ec0** (the promotion of `bonnor_ebert_count`): its commit message quoted the skip marker of the new PROMPT note, and GitHub skips a push whose head message contains it anywhere.
- Local Lean: elan + `lake exe cache get` ≈ 6 min; `checked-build` of 44329974789 (7717f08) ≈ 3 min download, restored with DELETE_ZIP=1 (3.9 GB left); `lake build Checked` to main ≈ 5 min.

## Bottleneck (and what a yes/no changes)
- Four promotions (runs 1028Z, 1628Z and earlier) wait for one main run green on every job, and the checked job is close to its 240-min limit: 211 min for 7d5b41c, 180 min for 7717f08. Job log 134891775171: build 10 min (lake cache hit), **leanchecker 140 min single-threaded**, axiom audit 1 min, trust steps 20 min. On 2026-11-12 the same replay took 47 min. Question: can the replay be spread over parallel jobs with no change to what it checks? Yes → the checked job drops to ≈ 45 min and every later job stops waiting hours behind it; no → the checked job crosses 240 min within days and no promotion can be judged.

## What we did
1. Root cause of the missing CI run for 1473ec0 found; `scripts/check_commit_msg.py` (`--final` / `--skip`, 7 selftest controls; it flags 1473ec0's message) and a PROMPT note: the final message carries no skip marker at all.
2. Local measurement of `LEAN_NUM_THREADS` on the replay of 18 Chemistry modules (2 cores, 8 GB): one thread 43 s (user 24 s, sys 14 s), two threads slower (memory 5 GB, I/O wait): the per-module tasks each import the full environment, so threads inside one job do not help on a small machine.
3. `scripts/leanchecker_shard.py`: every tracked `Checked/**/*.lean` plus `Checked.lean` (638 modules), shard i = FNV-1a hash mod 4 (as nanoda's `ShardMain.lean`), `lake env leanchecker <modules>`; selftest: the shards partition the module list for k = 1, 2, 4 (147, 152, 178, 161 modules; olean sizes 1.06, 1.17, 1.05, 0.91 GB). Workflow: lean-action's `leanchecker: "false"` in the checked job and a new matrix job `leanchecker` (4 shards, own concurrency groups, 240-min limit, pass memoised on the exact input hash like nanoda); `scripts/ci_changes.py` hashes the shard script too. Branch trial `wip/leanchecker-shards` (8222d87), run 44373171551 (section End).
4. Part 1 (rotation): `Checked/Trust/NecessityAU.lean`. `margChi_ge`: by the closed form, the marginalised chi-square is at least chi-square plus prior term at one value of the Hubble constant; `row_ge`: at least the row z = 2.3 (H = 224 ± 8); `lo_bound`/`hi_bound`: for Ω ≤ 0 the model factor there is at most 1, for Ω ≥ 1 at least 5.99, and row plus prior is at least 50 for both priors; so no Ω outside [0, 1] is below the certified interior values 18.21 and 20.62. Hence `0 ≤ Ω` and `Ω ≤ 1` are REDUNDANT (each alone) in `fr13_bestfit68`, `fr13_bestfit738`, `fr13_minval68`, `fr13_minval738`, `fr13_zda68`, `fr13_zda738` (12), and the minimiser condition is NEEDED in `fr13_minval68`, `fr13_minval738` (Ω = 0: chi-square ≥ 50). No certificates; ≈ 20 min, four compiles.

## Measure
- Necessity: REDUNDANT 187 → 199, NEEDED 695 → 697, open 121 → 107; the six FR13 headlines fully classified.
- Judge: checked job's replay 140 min single-threaded → four shards (times in End).

## End
(filled at the end of the run)

## Next
(filled at the end of the run)
