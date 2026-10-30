# STATE

Last updated: 2026-10-30, run 2026-10-30T1428Z (scheduled).

## Phase
S1, S2 DONE. Working target 1 (cosmography). Verified findings F1–F9.

## Target 1: Cosmography: low-redshift (Hubble-series) expansions in FLRW
Case and the eight items: `TARGETS.md` #1 (unchanged).
Bottleneck now: the hub (Bamba et al. 2012 review) is nearly exhausted: open items C14 (η numbers, Sec. XI, two routes), C10 (R⁴_D, R⁵_D, two routes), C12 (misprint, not formalizable without an F(R) model with F″ ≠ 0), C8 (one route). Positive: C14 is a wrong numerical claim in the paper's own conclusion section; negative: its conclusion ("η small") survives, so low consequence. After C14/C10 a new source family is needed (TARGETS.md items 2–8 or a new hub).

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
- **PROVED** (F9) `Checked.Cosmography.FRCosmo.fR_values` (metric F(R) FLRW: R·F(R₀) = −6H₀²(P₀Ω+Q₀) etc. with the corrected R, every model, no nondegeneracy), `curv_derivs` (correct (11.10)–(11.13)), `exists_LCDM_model`, `printedR3Claim_false`, `printedF0Mul_false_at`, `printedF0ClaimMul_false`, `printedF0_false_at`, `printedF0Claim_false`. Audit `runs/2026-10-30T1428Z/audit.md`. Promotion 2d0fae5, CI 41079704808 green (incl. nanoda).
- **Findings F1–F9** (FINDINGS.md): all verified and reported to Alexander (F9 this run).
- C8 one route. C10 (R⁴_D, R⁵_D): two routes (referees 1028Z, 1232Z). C12, C14: two routes (screen 1232Z; blind/referee 1428Z). C11, C13 → F9.

## Environment (this run)
- Repo pre-cloned (add_repo not exposed; not needed); local main was stale (reset to origin/main). Pushes verified (remote head = local each time).
- Local Lean: elan + `lake exe cache get` (~3 min); FRCosmo elaborates in ~10 s.
- CI (read by ID): previous run's last 41069186273 green; LOCK 41071807029 green; freeze 4ff3816 (41073073503) green; Work proofs 1df6387 (41078117151), 5adf870 (41078660695) green; blind closure c849eb5 (41079150781) green; promotion 2d0fae5 (41079704808): both jobs green (build, leanchecker, axiom-audit, nanoda 7.3 min, no-sorry check; checked job 13.8 min). Records/LOCK-removal commit: read next run.

## Daily review (53.3), 2026-10-30
- AUDITED + PROVED headlines in last 24 h: 2 (0028Z) + 5 (0220Z) + 5 (0430Z) + 5 (0628Z) + 9 (0828Z) + 12 + 6 (1028Z) + 10 (1232Z) + 8 (1428Z). Findings: F1–F9 verified.
- Bottleneck history: candidate supply (0628Z) answered by hub screening; curvature tooling (1028Z–1232Z); F(R) machinery (1428Z). Next bottleneck: a new source family.
- Patterns fixed run 1428Z: HasDerivAt combinator shape (PROMPT note); differentiate-eventual-identity pattern recorded. 1232Z experiments evaluated: keep.
- Honest check: F1–F9 are formula misprints in one hub and its upstream papers; numbers in those papers were mostly unaffected. The checked general theorems (cosmographic series, F(R) closure) are the durable value. Next: aim at results people compute with (TARGETS.md).

## Known gaps
- Cosmetic linter warnings in generated proofs. Leave.
- nanoda step ~6.5 min in CI 41034616298, 8.2 min in 41066721346 (checked job 15 min total). Watch; if CI > 20 min, split heavy imports or run nanoda per module.
- F4's Lean result is the flat instance; its curved sign error now follows from F6's general theorem (corrected D² is part of `lumDist_y_fifth_order`), but no separate curved refutation of the printed D² is stated. F5 flat only.

- F9: the printed F″, F‴ relations (11.23)–(11.24) (with the printed R) are not refuted in Lean: both sides vanish in ΛCDM; a model with F″(R₀) ≠ 0 would be needed (ODE existence for a given F).

## Open questions for Alexander
None. F9 sent as information (any contact with authors is his call, 47.1).

## Exact next step
1. Read CI of this run's records/LOCK-removal commit by ID; evaluate the run-1428Z LEDGER experiment (combinator shape).
2. C14 (prep: `runs/2026-10-30T1428Z/scripts/prep_c14.py` gives the derived dη/dε; printed η₂₀ numerator agrees, denominator does not) (why: wrong numbers in the paper's own conclusion section (11.42)–(11.45), two routes): Lean statement on the paper's own printed formulas: with q, j, s, l = ΛCDM·(1+ε), the ε-derivative at 0 of F″(R₀)H₀⁴/F(R₀) = (P₂Ω+Q₂)/(36(P₀Ω+Q₀)) (from `fR_values`, R cancels) is −2(27Ω²+24Ω−32)/(27Ω(Ω−2)(27Ω²+60Ω+112)), not the printed (11.42); η₃₀ likewise; numbers at Ω = 0.041, 0.25. Pure algebra + `HasDerivAt` of a rational function; reuse `fR_values` to tie it to the physics. Freeze first; launch blind + referee at freeze.
3. C10 (R⁴_D, R⁵_D, two routes) via `littleO_of_hasDerivAt`.
4. Then pick the next source family (TARGETS.md items 2–8, or a new hub screened by a subagent) — the Bamba review is nearly exhausted.
Blocking: nothing.
