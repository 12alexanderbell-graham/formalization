# Run 2026-11-20T0028Z

**THE RESULT:** part 1 by rotation (STATE 2e → part 1 as in section Next of `runs/2026-11-19T1828Z/README.md`, trust track T2b). Eighteen hypotheses of listed statements are shown NEEDED by Lean theorems with counter-examples (section What we did): the condition at infinity of twelve boundary-layer statements, through one new global solution on the whole half-line.

**What can a scientist now trust without checking it themselves, that they could not before?** For seventeen more hypotheses (the velocity tending to one far from the wall, in the window, uniqueness and monotone statements of five boundary-layer problems) and one wall condition, a Lean theorem that the statement fails without it; twelve more statements have every hypothesis classified.

**Weakest unchecked step:** the hypotheses still listed open in `TRUST_MAP.md` (section Next); the judge's slowest job is still nanoda shard 1 (section Next).

## Start
- 00:28Z. Local main was a stale divergent shallow clone; reset to origin/main d363b3d. No LOCK → taken (8e4f476).
- CI at start: 44640560624 (d363b3d, promotion of `laneEmden72_constants`) running; read in section CI read.
- Local Lean: elan + Mathlib cache ≈ 3 min; `checked-build` of 44619914467 (1870169) restored with DELETE_ZIP=1 (the artifact of d363b3d was not yet uploaded); `~/.cache/mathlib` deleted first (20 GB free after). 8 GB of memory, no swap; the four index-seven-halves data parts rebuilt one at a time by lake (≈ 2.5 min each, ≈ 4 GB).

## Bottleneck (and what a yes/no changes)
- Part 1: the condition at infinity (p → 1) is the open hypothesis shared by twelve listed statements (the monotone windows, the limit windows and both conditions of each limit-uniqueness statement, for Hiemenz, Homann and three Falkner–Skan wedges), open since they were listed because a witness needs a solution on the whole half-line that does not tend to one. Does one global solution with a free wall shear exist in Lean? Yes → seventeen hypotheses close in one run; no → record where the global argument breaks.

## What we did
- **Float scan first** (`scipy`, not evidence; Hiemenz, q(0) from 0.5 to 3): every wall shear above the window gives exponential growth, p ≈ C e^{aη}, q/p → a, f/p → 1/a (consistent at leading order: f q and p² cancel); every wall shear below it turns over (p < 0) and then also grows exponentially. No closed form (sympy on six families of exponential, hyperbolic and trigonometric ansätze).
- **A global solution in Lean** (`Checked/Trust/ExpFlow.lean`, new mathematics, ≈ 35 min, every lemma compiled the first or second time): for every c in [1, 2] and β in (0, 1] the system f' = p, p' = q, q' = −c f q + β (p² − 1) has a solution on [0, ∞) with f(0) = p(0) = 0, q(0) = 10 and q > 0 throughout (`exists_wall_ten`). Construction: the field clamped at the level `M t = 100 e^{20t}` is Lipschitz on every [0, T] (`lip`, constant 6 M(T) + 1), so Picard–Lindelöf gives a solution on each [0, T] glued by uniqueness (`exists_sol`, the `HExFlow` pattern with a growing clamp). The clamps are never active, by continuous induction (`cont_ind`: positivity at a and positivity at each later t from positivity before it give positivity on [a, b], via the infimum of the failure set — no openness needed) twice:
  - on [0, 1/5] (`phase1`): with 8 < q < 12 before t, p ∈ [8s, 12s], f ∈ [4s², 6s²] and q(t) ∈ [10 − 7t, 10 + 6t] ⊂ (8, 12);
  - after 1/5 (`phase2`): the region q > 0, f > 0, w = 20 p − q > 0, f < M, 20 p < M is kept: with v = 20 c f − β p (v′ ≥ w > 0, so v ≥ 4/5), the exact identity w′ = 400 p + p v + β − (20 + c f) w gives (w e^{Cs})′ ≥ 0 with C = 20 + 2F (F the bound of f on [1/5, t]); q′ ≥ −c f q gives (q e^{2Fs})′ ≥ 0; (p e^{−20s})′ = −w e^{−20s} ≤ 0 gives p ≤ (12/5) e^{20s}; then f ≤ 6/25 + (3/25) e^{20s}. Every positivity at t comes from a monotone function on [1/5, t], never from a derivative at the first exit time.
- **Witnesses** (`Checked/Trust/NecessityBB.lean`, emitted by `runs/2026-11-20T0028Z/scripts/emit_ncbb.py`): hypothesis 6 (p → 1) NEEDED in `hiemenz_limit_window`, `homann_limit_window`, `fs_half_limit_window`, `fs_fifth_limit_window`, `fs_tenth_limit_window` (wall shear ten is outside every window), in `hiemenz_monotone_window`, `homann_monotone_window` (the solution's shear is positive throughout, so the monotone hypothesis still holds), and hypotheses 6 and 12 in the five `*_limit_equal` statements (the solution beside the solution of each `*_exists_bounded` headline: their wall shears differ). Hypothesis 7 (p(0) = 0) of `fs_monotone_of_limit` NEEDED by the uniform stream f = η, p = 1, q = 0 (zero shear). Every witness compiled the first time.
- Axioms of every new theorem: propext, Classical.choice, Quot.sound (StatementDeps).

## Measure
- Necessity: NEEDED 722 → 740, open 79 → 61; fully classified headlines 125/177 → 137/177 (StatementDeps of the final tree).
- Experiment of run 1828Z (ported stacks with a free start for statements on [0, ∞)): not evaluated (this run took the conditions at infinity, which need no ported stack: the global solution is new and generic in c and β).

## CI read
- 44640560624 (d363b3d, promotion of `laneEmden72_constants`) concluded green on every job at 01:20Z: checked job, work job, leanchecker 4/4, nanoda 4/4 (nanoda step with export: shards 0–3 35, 67, 48, 45 min; shard 1 was 81 min in 44611137609) → PROVED; STATE heading with the judged template; Alexander told (L.2).

## End
- Local before the final push: `lake build Checked` (3720 jobs; the four index-seven-halves data parts ≈ 2.5 min each), StatementDeps relock (302 headlines, NV 182/182; necessity NEEDED 722 → 740, REDUNDANT 218, open 79 → 61; fully classified 125/177 → 137/177; frozen registry: new entries only), Claims (302 generated claims), open baseline updated (`necessity_open_baseline.txt`: twelve lines removed, `fs_monotone_of_limit` 2, 3, 6, 8), validation packet regenerated, check_prose, precheck_citations, check_status_lines, goal guard, check_necessity and check_headline_mentions `--base d363b3d`, records_check.py d363b3d (see the final commit message).

## Next
- CI read first: the run of this run's final push (two new Trust modules `ExpFlow`, `NecessityBB`; no headline changed). Green on every job → nothing to promote; red → `python3 scripts/trust/records_check.py <base>` or `local_frozen_step.py --trust <base>`.
- Nanoda shard 1 (67 min in 44640560624, the slowest job; shards 0: 35 min): find the declarations that dominate it (one export per module of shard 1 with one worker, or the checker per module group as `leanchecker_shard.py` does), then rebalance on nanoda's own times.
- Then by rotation (part 1 at 0028Z, parts 2/5 at 2228Z, part 3 at 2028Z): part 3 as in section Next of `runs/2026-11-19T2028Z/README.md`; parts 2/5 as in section Next of `runs/2026-11-19T2228Z/README.md`. Part 1 later: with the `ExpFlow` pattern (LEDGER experiment of this run) `fs_monotone_of_limit` 8 (a global solution whose shear turns negative: the float scan below the Hiemenz window turns over and then grows exponentially, so the same invariant region applies after the turn) and 6 (a wall value of f); the wall conditions of `fs_neg_reversed_printed_overshoots` (4, 5) and `fs_separation_below_printed` (4, 5); `eta_ratios` 3, 4 and the B1 lower density bounds as in section Next of `runs/2026-11-19T1228Z/README.md`.
