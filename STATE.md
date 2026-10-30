# STATE

Last updated: 2026-10-30, run 2026-10-30T1028Z (scheduled).

## Phase
S1, S2 DONE. Working target 1 (cosmography). Verified findings F1–F7.

## Target 1: Cosmography: low-redshift (Hubble-series) expansions in FLRW
Case and the eight items: `TARGETS.md` #1 (unchanged).
Bottleneck now: candidate supply in the cosmography hub. Sec. X of the review is now checked except C9 (z-series D⁴_L, D⁴_A missing K²/120, partly the review's own O(χ⁵) truncation) and C10 (R⁴_D, R⁵_D). Positive for the Sec. XI screen: new candidates for the same pipeline; negative: the hub is exhausted and target 1 needs a new source family.

## Results (statuses, annex XXXVIII)
- **PROVED** `Checked.Cosmography.lookback_second_order`, `..._bigO`: run 0028Z.
- **PROVED** (F1) `Checked.Cosmography.Aviles.flatLCDM_coeffs`, `avilesL0Claim_false`, `avilesM0Claim_false`, `AvilesWitness.printedL0_false_at`, `printedM0_false_at`: run 0220Z.
- **PROVED** (F2) `Checked.Cosmography.CPL.flatCPL_coeffs`, `printedL0_ne`, `clsL0Claim_false`; `CPLExistence.exists_flatCPL`, `printedL0_false_at`, tool `exists_local_model`: run 0430Z (CI 41007523313, 41007796446 green).
- **PROVED** (F3) `Checked.Cosmography.CCS.lookback_fifth_order`, `printedD4_fails`, `printedD4_fails_past`, `ccsD4Claim_false`, `ccsD4ClaimPast_false`: run 0628Z (promotion dac809b, CI 41019261348 green).
- **PROVED** (F4) `Checked.Cosmography.BambaY.lumDist_y_third_order` (flat d_L(y) to y³, any C³ a, d_L from ∫dt/a), `printedD2y_fails`, `printedD2y_fails_past`, `bambaD2yClaim_false`, `bambaD2yClaimPast_false`. Audit `runs/2026-10-30T0828Z/audit.md`. Promotion c22016e, CI 41034616298 green (build, leanchecker, axiom-audit, nanoda).
- **PROVED** (F5) `Checked.Cosmography.CVdQ.dQ_y_third_order` (flat d_Q(y) to y³), `printedQ2_fails_past`, `cvdQClaim_false`, `cvdQClaimPast_false`. Audit same file, section C1. Promotion 2d9e567, CI 41036122533 green (build, leanchecker, axiom-audit, nanoda).
- **PROVED** (F6) `Checked.Cosmography.BambaK.lumDist_y_fifth_order` (curved d_L(y) to y⁵, every real K, any C⁵ a), `printedD3y_fails[_past]`, `printedD4y_fails[_past]`, `bambaD3yClaim[Past]_false`, `bambaD4yClaim[Past]_false`, `milne_printedD3y_fails_past`, `milne_printedD4y_fails_past`, `printed_flat_eq`; helper `Checked.Cosmography.Transverse.transverse_expansion`. Audit `runs/2026-10-30T1028Z/audit.md`. Promotion CI: see Environment.
- **PROVED** (F7) `Checked.Cosmography.BambaA.angDist_y_fifth_order` (curved d_A(y) to y⁵), `printedDA3_fails[_past]`, `printedDA4_fails[_past]`, `bambaDA3Claim[Past]_false`, `bambaDA4Claim[Past]_false`, `milne_printedDA4_fails_past`. Audit same file, §C7.
- **Findings F1–F7** (FINDINGS.md): all verified and reported to Alexander (F6, F7 this run, with the F4 provenance correction).
- C8 one route. C9 (z-series D⁴ K²/120), C10 (R⁴_D, R⁵_D): one route each (referee run 1028Z).

## Environment (this run)
- Repo pre-cloned (add_repo not exposed; not needed). Pushes verified (remote head = local each time).
- Local Lean: elan + `lake exe cache get` (~3 min); BambaCurved elaborates in ~35 s; full `lake build Checked Work` from a fresh box ~15 min (Work audit files import Mathlib).
- CI (all green, read by ID): C6 freeze b485344 (41041698955), proofs be8b84d (41042754470), C6 promotion 76e6e64 (41048210895: build, leanchecker, axiom-audit, nanoda); C7 freeze 4337b9b (41048344960), proofs 8e2df42 (41048549262), C7 promotion 0a5db51 (41051129131). LOCK-removal commit: read next run.

## Daily review (53.3), 2026-10-30
- AUDITED + PROVED headlines in last 24 h: 2 (0028Z) + 5 (0220Z) + 5 (0430Z) + 5 (0628Z) + 9 (0828Z) + 12 + 6 (1028Z). Findings: F1–F7 verified.
- Bottleneck history: candidate supply (0628Z) answered by hub screening; now curvature tooling.
- Patterns fixed run 0828Z: heartbeat trap; MVT tool; referee as second route. Run 1028Z: truncated-series algebra (`approx_mul`), `unfold` order, subagent file hygiene (LEDGER experiments; evaluate next run).

## Known gaps
- Cosmetic linter warnings in generated proofs. Leave.
- nanoda step ~6.5 min in CI 41034616298. Watch; if CI > 20 min, split heavy imports or run nanoda per module.
- F4's Lean result is the flat instance; its curved sign error now follows from F6's general theorem (corrected D² is part of `lumDist_y_fifth_order`), but no separate curved refutation of the printed D² is stated. F5 flat only.

## Open questions for Alexander
None. F6, F7 sent as information (any contact with authors is his call, 47.1).

## Exact next step
1. Read CI of this run's last commits by ID (C7 promotion + records); evaluate the run-1028Z LEDGER experiments (approx algebra: C7 compiled first try; C9 is the next test).
2. C9 (why: last open item of Sec. X, decides how much of the review's curvature block is the (10.30) truncation): z-series D⁴_L, D⁴_A (10.43)–(10.44), (10.50)–(10.51) miss +K²c⁴/(120H₀⁴a₀⁴). Freeze claims (charitable: also the reading "valid to O(χ⁵) only" — state it and decide whether the claim is refutable under it); prove a z-version of `lumDist_y_fifth_order` (substitute y = z/(1+z): truncated powers of z/(1+z) with `approx_pow`, or rerun gen_curved.py with N_k = truncated (B−1)^k as in CCS); refute.
3. Screen Sec. XI of 1205.3421 (pp. 112–125) with the run-0628Z brief (whole equation blocks; file hygiene note in PROMPT).
4. Optional: C10 (R⁴_D, R⁵_D) via `littleO_of_hasDerivAt`.
Blocking: nothing.
