# STATE

Last updated: 2026-10-30, run 2026-10-30T1028Z (scheduled).

## Phase
S1, S2 DONE. Working target 1 (cosmography). Verified findings F1–F6.

## Target 1: Cosmography: low-redshift (Hubble-series) expansions in FLRW
Case and the eight items: `TARGETS.md` #1 (unchanged).
Bottleneck now: turning the general curved d_L(y) theorem (F6) into the remaining Sec. X candidates: C7 (d_A,y, a corollary via d_A = d_L(1−y)²) and C9 (z-series D⁴_L, D⁴_A missing K²/120). Positive: two more checked items from one theorem, and the review's whole y/z distance block audited. Negative: the referee's side derivations would be wrong.

## Results (statuses, annex XXXVIII)
- **PROVED** `Checked.Cosmography.lookback_second_order`, `..._bigO`: run 0028Z.
- **PROVED** (F1) `Checked.Cosmography.Aviles.flatLCDM_coeffs`, `avilesL0Claim_false`, `avilesM0Claim_false`, `AvilesWitness.printedL0_false_at`, `printedM0_false_at`: run 0220Z.
- **PROVED** (F2) `Checked.Cosmography.CPL.flatCPL_coeffs`, `printedL0_ne`, `clsL0Claim_false`; `CPLExistence.exists_flatCPL`, `printedL0_false_at`, tool `exists_local_model`: run 0430Z (CI 41007523313, 41007796446 green).
- **PROVED** (F3) `Checked.Cosmography.CCS.lookback_fifth_order`, `printedD4_fails`, `printedD4_fails_past`, `ccsD4Claim_false`, `ccsD4ClaimPast_false`: run 0628Z (promotion dac809b, CI 41019261348 green).
- **PROVED** (F4) `Checked.Cosmography.BambaY.lumDist_y_third_order` (flat d_L(y) to y³, any C³ a, d_L from ∫dt/a), `printedD2y_fails`, `printedD2y_fails_past`, `bambaD2yClaim_false`, `bambaD2yClaimPast_false`. Audit `runs/2026-10-30T0828Z/audit.md`. Promotion c22016e, CI 41034616298 green (build, leanchecker, axiom-audit, nanoda).
- **PROVED** (F5) `Checked.Cosmography.CVdQ.dQ_y_third_order` (flat d_Q(y) to y³), `printedQ2_fails_past`, `cvdQClaim_false`, `cvdQClaimPast_false`. Audit same file, section C1. Promotion 2d9e567, CI 41036122533 green (build, leanchecker, axiom-audit, nanoda).
- **PROVED** (F6) `Checked.Cosmography.BambaK.lumDist_y_fifth_order` (curved d_L(y) to y⁵, every real K, any C⁵ a), `printedD3y_fails[_past]`, `printedD4y_fails[_past]`, `bambaD3yClaim[Past]_false`, `bambaD4yClaim[Past]_false`, `milne_printedD3y_fails_past`, `milne_printedD4y_fails_past`, `printed_flat_eq`; helper `Checked.Cosmography.Transverse.transverse_expansion`. Audit `runs/2026-10-30T1028Z/audit.md`. Promotion CI: see Environment.
- **Findings F1–F6** (FINDINGS.md): all verified and reported to Alexander (F6 this run, with the F4 provenance correction).
- Candidate C7 (Eqs. 10.61–10.63, d_A,y curvature terms; also 0902.0088 Eqs. 62–64): three routes, Lean pending. C8 one route. C9 (z-series D⁴ K²/120), C10 (R⁴_D, R⁵_D): one route each (referee run 1028Z).

## Environment (this run)
- Repo pre-cloned (add_repo not exposed; not needed). Pushes verified (remote head = local each time).
- Local Lean: elan + `lake exe cache get` (~3 min); BambaCurved elaborates in ~35 s; full `lake build Checked Work` from a fresh box ~15 min (Work audit files import Mathlib).
- CI: LOCK e4f9837 (41041055001); freeze b485344; proofs be8b84d; promotion and records: CI_PLACEHOLDER.

## Daily review (53.3), 2026-10-30
- AUDITED + PROVED headlines in last 24 h: 2 (0028Z) + 5 (0220Z) + 5 (0430Z) + 5 (0628Z) + 9 (0828Z) + 12 (1028Z). Findings: F1–F6 verified.
- Bottleneck history: candidate supply (0628Z) answered by hub screening; now curvature tooling.
- Patterns fixed run 0828Z: heartbeat trap; MVT tool; referee as second route. Run 1028Z: truncated-series algebra (`approx_mul`), `unfold` order, subagent file hygiene (LEDGER experiments; evaluate next run).

## Known gaps
- Cosmetic linter warnings in generated proofs. Leave.
- nanoda step ~6.5 min in CI 41034616298. Watch; if CI > 20 min, split heavy imports or run nanoda per module.
- F4's Lean result is the flat instance; its curved sign error now follows from F6's general theorem (corrected D² is part of `lumDist_y_fifth_order`), but no separate curved refutation of the printed D² is stated. F5 flat only.

## Open questions for Alexander
None. F6 sent as information (any contact with authors is his call, 47.1).

## Exact next step
1. Read CI of this run's last commits by ID (promotion + records commit); evaluate the run-1028Z LEDGER experiments.
2. C7 in Lean (why: completes the review's y-series block with checked evidence): freeze claims for (10.61)–(10.63) (printed D³_{A,y}, D⁴_{A,y}; D_{A,y}⁰⁻² are right) in a new `Work/Cosmography/BambaAngular.lean`; d_A := lumDist/(1+z)²; theorem: H₀d_A − SA(y) = (1−y)²·remK(correct) + y⁶·poly(y), so o(y⁵) from `lumDist_y_fifth_order`; refute with a = eᵗ, K = 1 (D³ diff 1/4, D⁴ diff 9/20; Milne refutes only D⁴). Correct coefficients: FINDINGS C7 row. Then blind + referee + promote.
3. C9 (z-series D⁴_L, D⁴_A missing +K²/120): same pipeline in z (substitute y = z/(1+z), or N_k = truncated (B−1)^k as in CCS).
4. Screen Sec. XI of 1205.3421 (pp. 112–125) with the run-0628Z brief (whole equation blocks; file hygiene note in PROMPT).
Blocking: nothing.
