# Run 2026-11-08T1228Z (scheduled)

**THE RESULT:** parts 2 and 5 moved: the Hiemenz and Homann stagnation-point theorems now speak about a class a reader can check on the velocity profile, −1 ≤ f' ≤ 1, instead of the condition f'' > 0 on the unknown's second derivative, and they say *the* solution: every solution in the class has its wall shear in the certified ten-decimal window, any two are equal on [0, ∞), and one exists (with 0 ≤ f' < 1). Frozen, proved, audited (blind restatement closed in full, blind literal reading of the bounds, referee) and promoted to Checked in one run, with no new numerical certificate. Also an audit finding: run 1028Z's referee claim "f' < 1 ⟺ f'' > 0" has a gap at f' ≤ −1.

**What can a scientist now trust without checking it themselves, that they could not before?** That the Hiemenz problem f''' + f f'' + 1 − f'² = 0 (and Homann's, f''' + 2 f f'' + 1 − f'² = 0), f(0) = f'(0) = 0, f' → 1, has exactly one solution whose velocity ratio f' stays between −1 and 1, and that its wall shear lies in (1.2325876568, 1.2325876569), resp. (1.3119376938, 1.3119376939) — without having to know beforehand that the solution's f'' is positive.

**Measure:** Checked headlines 198 → 204 (non-vacuity witnessed 129 → 133); blind restatement closed 6/6 (run 1028Z's: 5/7, existence open); new tools ≈ 200 lines (fencing + ODE uniqueness), certificate cost zero; auditor role → promotion ≈ 2 h, of which the full local `lake build Checked` ≈ 75 min on 2 cores.

**Weakest unchecked step:** whether f' < 1 alone suffices (unproved; ≈ 6 200 shooting values per k without a counterexample; the classical unrestricted uniqueness for β < 1 is read second-hand only). Second: the β = 1/2 Falkner–Skan row still says "a solution" (scratch for the scaled version compiled: `lean/FSHalfBounded.lean`).

## Start
- 12:27Z. Pre-cloned checkout detached with a stale local `main`; `git reset --hard origin/main` (local only) = c8c8253.
- LOCK: run 2026-11-08T1028Z, taken 10:37Z, heartbeat 12:05Z (alive, < 150 min) → rule 48.4: auditor/referee role; writes only in this folder plus a CHANGELOG append; next-step theorem built as scratch Lean here (PROMPT working note "A live LOCK is not idle time").
- Environment: repo reachable (push access); local Lean: elan installer + `lake exe cache get` ok; CI: not read yet.

## Bottleneck
The newest frozen claims (1028Z: `MonotoneWindow`, `MonotoneExists`) are about solutions with q = f'' > 0 on [0, ∞). A reader cannot check that hypothesis on a solution they do not have; the literature's class is 0 < f' < 1 (Coppel 1960). Run 1028Z's referee (`runs/2026-11-08T1028Z/referee_mw.md` §1) proposed "given f' → 1, q > 0 ⟺ f' < 1". Yes (a proof in Lean) → the theorems speak about the class physicists use, and "same wall shear" becomes "the unique solution". No → the hypothesis stays a condition on f''.

## Audit finding on the referee's equivalence (1028Z, §1)
The referee's argument for "f' < 1 ⇒ q > 0" says "once q < 0, p decreases, p < 1 stays, so q' < 0 at every later zero". That step needs p² < 1, i.e. also p > −1: at a zero of q, q' = −1 + p², which is ≥ 0 when p ≤ −1. A solution whose f' dips below −1 is not excluded by the argument. What does hold, and is now compiled (below): **−1 < f' < 1 ⇒ q > 0**, and (with f'(0) = 0) **−1 ≤ f' ≤ 1 ⇒ −1 < f' < 1**. Whether f' < 1 alone suffices is not proved here (referee: numerically supported, ≈ 6 200 shooting values per k, no counterexample; likely implied by the classical unrestricted uniqueness for β < 1 — second-hand); no statement uses it.

## Scratch Lean (compiled with `lake env lean`, Mathlib only)
- `lean/BoundedPos.lean`: `pos_of_abs_lt_one` — for f' = p, p' = q, q' = −k f q − 1 + p² (any real k), p → 1 and −1 < p < 1 on [0, ∞) give q > 0 on [0, ∞). Fencing theorem with barrier 0 (`image_le_of_deriv_right_lt_deriv_boundary'`), then p non-increasing after a non-positive q contradicts p → 1.
- `lean/BoundedUnique.lean`: `eq_of_start` (two solutions with the same (f, p, q)(0) agree on [0, ∞): forward uniqueness, Lipschitz constant on the compact union of the two trajectories), `abs_lt_of_abs_le` (f'(0) = 0 and −1 ≤ f' ≤ 1 ⇒ −1 < f' < 1: a touch of ±1 at η₁ > 0 is an interior extremum, so f''(η₁) = 0, and backward uniqueness against the straight line f' ≡ ±1 forces f'(0) = ±1).

## After the LOCK release
- 1028Z released the LOCK in 9b97320 (it had promoted MonotoneWindow / MonotoneExists to Checked; its exact next step 2 is this widening). LOCK taken 12:53Z.
- Referee (`referee_bounded.md`, general-purpose subagent, on the scratch statements): **STANDS-WITH-CORRECTIONS** — statements and docstrings agree; derivations (a) q > 0 from |f'| < 1 for every k, (b) |f'| ≤ 1 ⇒ |f'| < 1 via the straight-line solutions, (c) uniqueness from the start values, all confirmed; the 1028Z gap is real; corrections were to this README's wording ("Coppel's class" was a misattribution: the classical restricted class is 0 < f' < 1; uniqueness in |f'| ≤ 1 is not claimed to go beyond the literature — for Homann, β = 1/2, it follows from the reported unrestricted uniqueness for β < 1; for β = 1 sources disagree). Applied above. Prior art read second-hand only (Veldman & van de Vooren 1980 quotes, arXiv 2011.07725); Coppel, Craven–Peletier, Hartman, Tam not read.

## Freeze → proof → audit → promotion
- 817c726: LOCK + brief of the blind literal reading (alone). 804a187: freeze (`Work/FalknerSkan/Bounded.lean`, all `sorry`; byte-identical to `lean/Bounded_frozen.lean`) + `Work/FalknerSkan/BoundedTools.lean`. Reading (Sonnet, `bound_reader/`) and blind restatement (Sonnet, `blind/`) in separate commits.
- 9920ce2: Work proofs (statements byte-identical), blind restatement closed in full (`Work/FalknerSkan/BBlindClosed.lean`, incl. existence with C³ via `ofSys`); axioms standard.
- Promotion (`scripts/promote_bd.py`): `Checked/FalknerSkan/BoundedTools.lean`, `Checked/FalknerSkan/Bounded.lean`, reader copy `Checked/Trust/SecondReadingBound.lean`, 4 NV witnesses, headlines, literal readings, audits (+8), vocabulary (`bounded`, `equal`), relock, TRUST_MAP, CLAIMS, packet; LEDGER.
- check_claim_vocab rejected the frozen names `*_bounded_unique` (V8: strength word) and their docstrings ("any two solutions": V1, V14): renamed `*_bounded_equal`, docstrings reworded before promotion (statements unchanged; LEDGER).
- Full local `lake build Checked` 13:11–14:18Z (first pass ended at Witnesses because the root module gained imports mid-build; incremental second pass green); StatementDeps with relock: 204 headlines, NV 133/133.

## CI
- 82833d9 (1028Z promotion, 42481874946): work and nanoda shards green; checked job cancelled by coalescing (a later push).
- 9920ce2 (this run's Work proofs, 42483811134): **green on every job** (completed 14:02Z), checked job included — its tree contains run 1028Z's promotion 82833d9, so the four monotone-solution headlines are PROVED. Next run: read the run of this run's promotion commit (Checked/FalknerSkan/Bounded*.lean).

## Next-step scratch
- `lean/FSHalfBounded.lean` (compiled): `fs_half_bounded_window`, `fs_half_bounded_equal` — Falkner–Skan β = 1/2 in the class −1 ≤ f' ≤ 1, by scaling to Homann with c = 1/√2 (`Checked/FalknerSkan/FSScale.lean`). Freeze it next.
