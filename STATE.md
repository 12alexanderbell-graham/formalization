# STATE

Last updated: 2026-10-30, run 2026-10-30T1232Z (scheduled).

## Phase
S1, S2 DONE. Working target 1 (cosmography). Verified findings F1–F8.

## Target 1: Cosmography: low-redshift (Hubble-series) expansions in FLRW
Case and the eight items: `TARGETS.md` #1 (unchanged).
Bottleneck now: turning the Sec. XI candidates (C11–C14, F(R) cosmography relations) and C10 into Lean results. Sec. X of the review is done except C10. Positive: findings in a different part of the review (modified gravity, not distance series); negative: Sec. XI misprints that do not affect results (C11, C12) are low value, so C13 (R fails the paper's own ΛCDM test) and C14 (η numbers) come first.

## Results (statuses, annex XXXVIII)
- **PROVED** `Checked.Cosmography.lookback_second_order`, `..._bigO`: run 0028Z.
- **PROVED** (F1) `Checked.Cosmography.Aviles.flatLCDM_coeffs`, `avilesL0Claim_false`, `avilesM0Claim_false`, `AvilesWitness.printedL0_false_at`, `printedM0_false_at`: run 0220Z.
- **PROVED** (F2) `Checked.Cosmography.CPL.flatCPL_coeffs`, `printedL0_ne`, `clsL0Claim_false`; `CPLExistence.exists_flatCPL`, `printedL0_false_at`, tool `exists_local_model`: run 0430Z (CI 41007523313, 41007796446 green).
- **PROVED** (F3) `Checked.Cosmography.CCS.lookback_fifth_order`, `printedD4_fails`, `printedD4_fails_past`, `ccsD4Claim_false`, `ccsD4ClaimPast_false`: run 0628Z (promotion dac809b, CI 41019261348 green).
- **PROVED** (F4) `Checked.Cosmography.BambaY.lumDist_y_third_order` (flat d_L(y) to y³, any C³ a, d_L from ∫dt/a), `printedD2y_fails`, `printedD2y_fails_past`, `bambaD2yClaim_false`, `bambaD2yClaimPast_false`. Audit `runs/2026-10-30T0828Z/audit.md`. Promotion c22016e, CI 41034616298 green (build, leanchecker, axiom-audit, nanoda).
- **PROVED** (F5) `Checked.Cosmography.CVdQ.dQ_y_third_order` (flat d_Q(y) to y³), `printedQ2_fails_past`, `cvdQClaim_false`, `cvdQClaimPast_false`. Audit same file, section C1. Promotion 2d9e567, CI 41036122533 green (build, leanchecker, axiom-audit, nanoda).
- **PROVED** (F6) `Checked.Cosmography.BambaK.lumDist_y_fifth_order` (curved d_L(y) to y⁵, every real K, any C⁵ a), `printedD3y_fails[_past]`, `printedD4y_fails[_past]`, `bambaD3yClaim[Past]_false`, `bambaD4yClaim[Past]_false`, `milne_printedD3y_fails_past`, `milne_printedD4y_fails_past`, `printed_flat_eq`; helper `Checked.Cosmography.Transverse.transverse_expansion`. Audit `runs/2026-10-30T1028Z/audit.md`. Promotion CI: see Environment.
- **PROVED** (F7) `Checked.Cosmography.BambaA.angDist_y_fifth_order` (curved d_A(y) to y⁵), `printedDA3_fails[_past]`, `printedDA4_fails[_past]`, `bambaDA3Claim[Past]_false`, `bambaDA4Claim[Past]_false`, `milne_printedDA4_fails_past`. Audit same file, §C7.
- **PROVED** (F8) `Checked.Cosmography.BambaZ.lumDist_z_fifth_order`, `angDist_z_fifth_order` (curved d_L(z), d_A(z) to z⁵, every real K, any C⁵ a), `printedDL4z_fails_past`, `printedDA4z_fails_past`, `bambaDLzClaim[Past]_false`, `bambaDAzClaim[Past]_false`, `milne_printedDL4z_fails_past`, `printed_flat_eq`. Audit `runs/2026-10-30T1232Z/audit.md`. Promotion f8251a4, CI: see Environment.
- **Findings F1–F8** (FINDINGS.md): all verified and reported to Alexander (F8 this run).
- C8 one route. C10 (R⁴_D, R⁵_D): two routes (referees 1028Z, 1232Z). C11–C14 (Sec. XI): one route each (screen run 1232Z).

## Environment (this run)
- Repo pre-cloned (add_repo not exposed; not needed); local main was stale (reset to origin/main). Pushes verified (remote head = local each time).
- Local Lean: elan + `lake exe cache get` (~3 min); BambaZ elaborates in ~30 s.
- CI (read by ID): previous run's last 41052780695 green; C9 freeze 8c553aa (41056879760) green, proofs 974b7a3 (41059379008) green, blind closure 0314608 (41059721770) green; promotion f8251a4 (41066721346): both jobs green (build, leanchecker, axiom-audit, nanoda 8.2 min, no-sorry check). LOCK-removal commit: read next run.

## Daily review (53.3), 2026-10-30
- AUDITED + PROVED headlines in last 24 h: 2 (0028Z) + 5 (0220Z) + 5 (0430Z) + 5 (0628Z) + 9 (0828Z) + 12 + 6 (1028Z) + 10 (1232Z). Findings: F1–F8 verified.
- Bottleneck history: candidate supply (0628Z) answered by hub screening; now curvature tooling.
- Patterns fixed run 1232Z: subagents (blind, referee, screen) launched together at freeze time; series transfer by exact identities (LEDGER experiments; evaluate next run). 1028Z experiments evaluated: keep.

## Known gaps
- Cosmetic linter warnings in generated proofs. Leave.
- nanoda step ~6.5 min in CI 41034616298, 8.2 min in 41066721346 (checked job 15 min total). Watch; if CI > 20 min, split heavy imports or run nanoda per module.
- F4's Lean result is the flat instance; its curved sign error now follows from F6's general theorem (corrected D² is part of `lumDist_y_fifth_order`), but no separate curved refutation of the printed D² is stated. F5 flat only.

## Open questions for Alexander
None. F8 sent as information (any contact with authors is his call, 47.1).

## Exact next step
1. Read CI of this run's last commits by ID (promotion f8251a4 if not recorded, LOCK-removal commit); evaluate the run-1232Z LEDGER experiments.
2. C13 (why: the printed R in the F(R₀) relation (11.31) fails the paper's own ΛCDM check (11.40) and de Sitter; highest-confidence Sec. XI candidate). Typeset-verify (11.31) and upstream 0802.1583 Eq. (33) yourself; at freeze, launch blind + referee + (optional) C14 check in ONE message. Lean: R(t) = −6(Ḣ + 2H²) (paper's sign), derivatives at t₀ as polynomials in a⁽ⁿ⁾(t₀)/a(t₀) and H₀ (pure algebra, `field_simp; ring`); state the paper's F(R₀) relation with its P₀, Q₀ (11.21)–(11.22) and refute at de Sitter / ΛCDM. Check how R enters (11.31) before freezing (the screen says R cancels in η₂₀, η₃₀).
3. C11, C12 (misprints in d³R₀/dt³ and Ḣ Ṙ sign; results unaffected): same Lean file, low priority; C14 (η₂₀, η₃₀ numbers) needs only the paper's own printed (11.21)–(11.30): sympy + Lean evaluation.
4. C10 (R⁴_D, R⁵_D, two routes) via `littleO_of_hasDerivAt`. (F2 provenance done this run: error already in 0802.1583 Eq. (40), 2008.)
Blocking: nothing.
