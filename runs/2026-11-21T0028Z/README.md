# Run 2026-11-21T0028Z

**THE RESULT:** part 1 by rotation (STATE 2q). The Lean theorems of this run and their statements are in section What we did.

**What can a scientist now trust without checking it themselves, that they could not before?** That four statements of the B1 family (the quartic fits with sources at 1 + z = 2√2 and 4√2) cost nothing in their lower density bound: for each a kernel theorem shows the statement with that hypothesis removed (section What we did; `TRUST_MAP.md` lists all four).

**Weakest unchecked step:** the regularity hypothesis of the Gelfand bound for every solution; this run found a gap in the route planned for it (section Next).

## Start
- 00:28Z. Local main was the stale divergent clone again (fa47717); `git checkout -B main origin/main` at bab83b4. No LOCK → taken (0cfaf6b).
- Env: repo ok (add_repo not exposed; the session clone was present). Local Lean installed with the official elan installer (v4.35.0), `lake exe cache get`, `checked-build` of 44831447919 (01c1905) restored by streaming; `lake build Checked` 3755 jobs. No subagents.
- CI at start: 44838711468 (bab83b4, run 2228Z's final push) in progress; read in section CI read.

## CI read
- 44838711468 (bab83b4): **green on every job** (23:42Z → 00:33Z; nanoda 4/4 and leanchecker 4/4 ran, none memoised) → `gelfand_pde_bound` PROVED: the judged template in its STATE.md heading; one L.2 line sent to Alexander.

## Bottleneck (and what a yes/no changes)
- Part 1 by rotation. Candidate of run 2228Z: hypothesis 1 of `gelfand_pde_bound`. Studied first (section Next): the route assumed u twice differentiable at every point of the ball, which the equation does not give in three dimensions. Switched to the next open item of the part: the lower density bounds of the B1 family (`TRUST_MAP.md`, 13 headlines with hypothesis 1 open). Can the four flat L19 headlines, whose conclusions rest only on a lower bound of the ratio of the two distances, be classified without a certified integral? Yes → four open items close with one comparison argument; no → the step that needs numerics is recorded.

## What we did
- **Part 1 (T2b): hypothesis 1 (`0 ≤ Ω`) of `B1L19.l19_sq_central`, `l19_sqg_central`, `l19_sq_box`, `l19_sqg_box` REDUNDANT** (`Checked/Trust/NecessityBI.lean`, `l19_sq_central_r1`, `l19_sqg_central_r1`, `l19_sq_box_r1`, `l19_sqg_box_r1`; local `lake build`, axioms propext, Classical.choice, Quot.sound). Each conclusion follows from `delta_ge`, whose only use of the density range is the ratio bound d_L(4√2) ≥ 2.84 d_L(2√2). For a negative density:
  - `bi_unreach`: if the radicand Ω(1+z)³ + 1 − Ω is negative at the farther source (here for Ω ≤ −1/63), no scale factor obeys the law back to it: the law gives a zero Hubble rate there, and at the first time the radicand reaches half its value at the source the mean value theorem gives a(τ) = a(t), a contradiction.
  - `bi_bridge`: the change of variables of `NCAQ.bridge` holds with a positive radicand at the source and Ω ≤ 1 (the radicand increases in v).
  - `bi_lower`, `bi_upper`, `bi_int_cube`: for Ω ≤ 0 the integrand divided by the empty-model integrand 2/v³ decreases in v, so with w = √(1/(2√2)) the integral from 1/2 to w is at least r(w)(4 − 2√2) and the integral from w to 1 at most r(w)(2√2 − 1).
  - `bi_ratio`: the intermediate value theorem gives a time s between the sources with a(s) = a₀/4; then d_L(4√2) ≥ √2 d_L(s) and (2√2 − 1)(A + B) ≥ 3B give d_L(4√2) ≥ 3.28 d_L(2√2) > 2.84 d_L(2√2). A bounce resting at the farther source (allowed for one negative density) only lengthens that distance, so no separate case is needed.
  - `bi_delta`: `delta_ge` for Ω < 0; each `_r1` theorem is the headline for Ω ≥ 0 and the headline's own proof with `bi_delta` for Ω < 0.
- **Annex LIV: `scripts/start_run.sh`.** Eleven runs in a row (2026-11-20T0028Z … this one) began by resetting the session's stale divergent `main` by hand, each with a different command, then installing elan and the Mathlib cache step by step. The script fetches, resets local main to origin/main only when every local commit is on some origin branch (else it stops and lists them), prints LOCK, installs elan and the cache if missing, and prints the restore steps that need the GitHub tools. Control: on this clone `git rev-list fa47717 --not --remotes=origin` is empty (the stale tip would be reset) and a second invocation is a no-op. PROMPT working note; LEDGER experiment.

## Records
- STATE.md, section Trust track status: the line of run 2026-11-18T0028Z below listed the lower bounds `0 ≤ Ω` of the flat L19 headlines among open items, which this run classifies; per the working note of run 2026-11-20T2028Z it is replaced by the generic hypotheses line and kept here verbatim:

> **Hypothesis necessity, density bounds of the B1 family (run 2026-11-18T0028Z; LEDGER; `Checked/Trust/NecessityAQ.lean`):** the bridge's upper density bound is REDUNDANT (a ≤ a₀ under the law, so v ≤ 1 and the radicand is positive) and its lower bound NEEDED (a bounce resting at its minimum at Ω = −1); the upper density bound is NEEDED in the five Ω ∈ [1/5, 2/5] headlines and the four flat L19 headlines, witnessed by the exact flat model a = sin^{2/3} (negative cosmological constant, Ω cos² t₀ = 1) at Ω = 2, 3/2 and 10 with one- or two-step bounds of the increasing integrand — no certified integral. Open in the family: the lower bounds 1/5 ≤ Ω (every miss still holds on [0, 1/5]: REDUNDANT-by-extension candidates), the lower bounds 0 ≤ Ω of the L19 headlines, the curved L19 pair, the fit-residual and coefficient hypotheses of `fit_direction` and `rl19_box_unmatched`, the curvature bounds of the curved L19 pair.

## Measure
- Necessity: REDUNDANT +4, open −4 (TRUST_MAP after this run's relock). The four flat L19 headlines now have hypothesis 1 classified.

## Local checks
- `lake build Checked` (3756 jobs), `#print axioms` of the four `_r1` theorems, `precheck_names.py`, `check_prose.py`, `precheck_citations.py`, `check_status_lines.py`, `TRUST_RELOCK=1 … StatementDeps.lean` (306 headlines, NV 185/185, necessity 750 / 227 / 54 open; a first relock ran before `lake build Checked` had rebuilt the root module and counted nothing new), `Claims.lean`, `validation/make_packet.py` (item 24 regenerated), `check_headline_mentions.py --base bab83b4`, `check_stale_necessity.py`, `records_check.py bab83b4` (43 commands; the first pass failed N1 until the four lines of `necessity_open_baseline.txt` were removed).

## Next
- CI read first: the run of this run's final push (one new Trust module `NecessityBI`; no headline changed). Green on every job → nothing to promote; red → `python3 scripts/trust/records_check.py <base>`.
- **Hypothesis 1 (C²) of `gelfand_pde_bound`, the gap found this run:** with λ > 0 the pointwise equation makes `fderiv ℝ u` differentiable at every point of the ball (Mathlib's Laplacian is zero where it is not), so g = fderiv ℝ u is continuous; but u itself may fail to be differentiable on a subset B of the zero set of g, and in three dimensions B need not be isolated (the one-dimensional argument of `NecessityBF` used radial symmetry). The maximum principle at a minimum point in B, and the mean value bounds along segments, both need B small on segments (countable suffices, by the countable-exception fundamental theorem `integral_eq_of_hasDerivWithinAt_off_countable`). Next step: show that u is differentiable at every point (for x in B, a direction d with Dg(x)d ≠ 0 exists since the trace is nonzero; whether that forces B to meet every segment in a countable set is the open question), or find a counterexample of Cantor type along a segment.
- Part 1 next: the lower density bounds `1/5 ≤ Ω` of `cubic_misses_z3`, `cubic_misses_z7`, `cubic_shape_miss`, `cubic_separation`, `cubic_direction` (floats this run: the misses grow as Ω decreases, at z = 3 from 0.17 at Ω = 1/5 to 1.06 at Ω = 0; the integrand decreases in Ω, so lower Riemann sums at five densities in [0, 1/5] and the polynomial at the left end of each subinterval should suffice; for Ω < 0 the integrand only grows, and at Ω = 0 the integral at z = 3 is exactly 3), and `1/10 ≤ Ω` of the curved pair.
- Parts 2/5 next: as in section Next of `runs/2026-11-20T2228Z/README.md`.
