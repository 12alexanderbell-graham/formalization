# Run 2026-11-18T1628Z (scheduled)

**THE RESULT:** parts 2 and 5 by rotation (STATE 1o → 1m). A new theorem in Checked (named in the body below) gives, for the isothermal sphere, the exact number of radii s ≥ 0 at which the dimensionless mass m(s) equals μ, for every μ > 0: zero above m(ξ₀), one at m(ξ₀), 2k + 2 between m(ξ₂ₖ₊₂) and m(ξ₂ₖ), 2k + 3 at m(ξ₂ₖ₊₂), one below m(ξ₁), 2k + 2 at m(ξ₂ₖ₊₁), 2k + 3 between m(ξ₂ₖ₊₁) and m(ξ₂ₖ₊₃), infinitely many at √(2/π); with m(ξ₀) ∈ [1.1822265, 1.1822266], m(ξ₁) ∈ [0.694366, 0.694367], m(ξ₂) ∈ [0.8306, 0.8308], m(ξ₃) ∈ [0.787992, 0.787995], m(ξ₄) ∈ [0.80091, 0.800916].

**What can a scientist now trust without checking it themselves, that they could not before?** How many isothermal gas spheres of a given mass, temperature and external pressure are in equilibrium, for every mass, as one kernel-checked count from the equation alone, with the masses where the count changes enclosed to six or seven digits for the first five of them.

**Weakest unchecked step:** the statement was read by the same model three times (referee, blind restatement, blind literal reader); the count and the windows are kernel-checked, and the referee's own integration is inside every window (smallest margin 2e-6, at m(ξ₄)).

## Start
- The theorem: `Checked.Math.BonnorEbertCount.bonnor_ebert_count`. Frozen 5f76575 before any proof, proved in Work 75a4b91; after the proof the first count clause was restated from `encard = 0` to `= ∅` (equivalent; `check_claim_vocab.py` V5 reads `√ … = 0` in one conclusion span as a junk value; LEDGER); promoted to Checked by the final push; referee STANDS; blind restatement closed in `Work/Math/BonnorEbertCountBlindClosed.lean`.
- 16:28Z. add_repo not exposed; checkout detached at 7717f08 = origin/main; `git checkout main` (fast-forward). No LOCK → taken (af32f61).
- CI at start: 44316709810 (d25cb3f): checked job cancelled (superseded), nanoda 0, 1, 3 green, shard 2 running. 44329974789 (7717f08): checked job in its build step since 15:28Z, nanoda shards waiting. Nothing judged.
- Local Lean: elan + `lake exe cache get` ≈ 4 min; `checked-build` of 44275141268 (7d5b41c) ≈ 3 min download, restored with FORCE=1 DELETE_ZIP=1 (a first restore was killed by a 2-minute tool timeout; run it in the background); `lake build Checked` to this run's tree ≈ 12 min (GLam modules).

## Bottleneck (and what a yes/no changes)
- STATE listed Bonnor–Ebert exact counts first for parts 2/5. Question: do the proved extrema (`bonnor_ebert_extrema_monotone`) and the five bounded-interval enclosures already determine the number of equilibria of every mass, with no new certificates? Yes → a complete count theorem for the classical Bonnor–Ebert problem in one run, and a reusable counting lemma for the Gelfand bands beyond λ₂.

## What we did
1. Freeze 5f76575 (`Work/Math/BonnorEbertCount.lean`): the class of `bonnor_ebert_extrema_monotone`; ∃ ξ strictly increasing → ∞ with the ξ₀ window, five value windows and m(ξ k) → √(2/π), and eight count clauses on `Set.encard {s ∈ Ici 0 | m s = μ}`. Blind restatement (Sonnet) and referee (Opus) in one message.
2. Referee STANDS (`referee/REPORT.md`): every clause true by hand; ξ uniquely pinned by the counts; the bands cover every μ > 0; own DOP853 integration m(ξ₀ … ξ₇) and N(μ) at ten masses agree; points R1 (bounded extremiser below S) and R2 (band-end variants), both met by the route.
3. Lean (`Work/Math/BonnorEbertCountMain.lean`, ≈ 25 min, four compiles): `count_abstract` for any continuous f with f(0) = 0 and strict alternating extrema (prepend 0, one root per segment by IVT and injectivity, induction, tails from the extremum properties); `ident_max`/`ident_min` identify the extremisers of `bonnor_ebert_max`, `_min`, `_second_max`, `_second_min`, `_third_max` with ξ₀ … ξ₄. Axioms propext, Classical.choice, Quot.sound.
4. Blind restatement closed first time (`HasDerivAt` → within, `neg_mul`). Blind literal reading (brief 4767ed7 → reading 2b760b63, `be_count_reader/`): indices 1, 2, 3, 4, next minimum 2k + 3, counts 0, 2k + 2, 2k + 3, 2k + 2, 2k + 3, 1 — every value agrees with the freeze.
5. Promotion `scripts/promote_be_count.py` (`#min_imports`: one Mathlib module); NV witness; necessity `Checked/Trust/NecessityAT.lean` (`glob_of_count`: the first two count clauses give the strict global maximum, so NecessityAJ's witnesses carry over: 1, 3, 4 NEEDED, 2 REDUNDANT); headlines, literal_readings; StatementDeps relock twice (the second after the V5 restatement and docstring words V1 found by `records_check.py`), Claims, CLAIMS_READER.

## Measure
- Headlines 296 → 297. Necessity NEEDED 692 → 695, REDUNDANT 186 → 187, open 121 (unchanged); fully classified 104/172 → 105/173.
- Bonnor–Ebert: number of equilibria known for every mass (before: extrema and monotone segments only).

## End
- See the final commit message for CI and local checks.

## Next
- CI read first: 44329974789 (7717f08; checked job running since 15:28Z, nanoda shards 2 and 3 cancelled by this run's mid-run push 75a4b91) and the run of this run's final push (promotion of `bonnor_ebert_count`: new Checked modules `BonnorEbertCountMain` (≈ 35 s locally), `BonnorEbertCount`, `SecondReadingBECount`, `NecessityAT`, Witnesses; nanoda must replay them). Green on every job for a736a0b or a descendant → `gelfand_pde_radial_count_values` PROVED (one L.2 line to Alexander); green for this run's final push → `bonnor_ebert_count` PROVED (one L.2 line). Red → `python3 scripts/trust/records_check.py <base>` or `local_frozen_step.py --trust <base>`; base 7717f08. Push intermediate commits with `[skip ci]` (PROMPT note of this run).
- Then by rotation (parts 2/5 at 1628Z, part 3 at 1428Z, part 1 at 1228Z): part 1 — as in STATE 1n. Part 3 later: as in STATE 1o. Parts 2/5 later: λ₃ of the Gelfand branch (fourth turning point near s ≈ 4532; one-sided cells beyond 429), so that `count_abstract` gives the Gelfand count on (λ₁, λ₃); the full Gelfand count for every λ > 0 as done here for Bonnor–Ebert (the turning sequence of `gelfand_extrema`, with λ(0) = 0, fits `count_abstract` directly; values beyond λ₂ open); Lane–Emden n = 3, 4.
