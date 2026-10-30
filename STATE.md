# STATE

Last updated: 2026-10-30, run 2026-10-30T0628Z (scheduled).

## Phase
S1, S2 DONE. Working target 1 (cosmography). Verified findings F1, F2, F3.

## Target 1: Cosmography: low-redshift (Hubble-series) expansions in FLRW
Case and the eight items: `TARGETS.md` #1 (unchanged).
Bottleneck now: finding more candidates worth checking (the broad screen is used up except C1). F2 and F3 both propagate into the Bamba et al. 2012 review: screen it formula by formula. Pipeline proven three times (F3 in one run); distance–redshift series now go through `CCS.inversion` (no derivative chains).

## Results (statuses, annex XXXVIII)
- **PROVED** `Checked.Cosmography.lookback_second_order`, `..._bigO`: run 0028Z.
- **PROVED** (F1) `Checked.Cosmography.Aviles.flatLCDM_coeffs`, `avilesL0Claim_false`, `avilesM0Claim_false`, `AvilesWitness.printedL0_false_at`, `printedM0_false_at`: run 0220Z.
- **PROVED** (F2) `Checked.Cosmography.CPL.flatCPL_coeffs` (flat matter + CPL: q₀, j₀, s₀, l₀ for every Ω, w₀, wₐ; C⁵ at t₀), `printedL0_ne`, `clsL0Claim_false` (model Ω=0, w₀=−1, wₐ=2/3, a = 1 − log(1−t)). Audit `runs/2026-10-30T0430Z/audit.md`. CI 41007523313 green (build, leanchecker, axiom-audit, nanoda 336194 decls).
- **PROVED** `Checked.Cosmography.CPLExistence.exists_flatCPL`, `printedL0_false_at`, tool `exists_local_model` (commit b6267ff, CI 41007796446 green: build, leanchecker, axiom-audit, nanoda 374957 decls). The printed CPL l₀ is now refuted at every parameter point with (1−Ω)(7−Ω)wₐ ≠ 0.
- **Finding F2** (FINDINGS.md): verified; referee STANDS-WITH-CORRECTIONS; reported to Alexander this run.
- **PROVED** (F3) `Checked.Cosmography.CCS.lookback_fifth_order` (lookback time to z⁵ for every C⁵ scale factor, correct D⁴), `printedD4_fails`, `printedD4_fails_past`, `ccsD4Claim_false`, `ccsD4ClaimPast_false`. Audit `runs/2026-10-30T0628Z/audit.md`. Promotion commit dac809b, CI 41019261348 (result below).
- **Finding F3** (FINDINGS.md): verified; referee STANDS; reported to Alexander this run.
- Candidate C1: typeset-confirmed as printed and wrong (sympy). Needs Lean evidence. R⁵_D misprint in CCS 2008 (A5): sympy + typeset only.

## Environment (this run)
- Repo pre-cloned in the session (add_repo not exposed as a tool; not needed). Pushes verified (remote head = local each time).
- Local Lean: elan + `lake exe cache get` (~3 min); CCSLookback elaborates in ~27 s; full `lake build` > 2 min (run in background).
- arXiv PDFs via curl; e-print robots-blocked (unchanged).

## Daily review (53.3), 2026-10-30
- AUDITED + PROVED headlines in last 24 h: 2 (0028Z) + 5 (0220Z) + 5 (0430Z) + 5 (0628Z). Findings: F1, F2, F3 verified.
- Bottleneck history: C1–C4 candidates since run 0028Z; three of four now verified findings. Next bottleneck is candidate supply.
- Patterns fixed run 0430Z: witness hunting (ODE existence); non-polynomial laws. Run 0628Z: series inversion tool; hub screening; records quote FINDINGS; commit attribution. LEDGER experiments.

## Known gaps
- Cosmetic linter warnings in generated proofs (unused simp args / push_cast). Leave.
- Import closure grew (ODE module): nanoda step 8 min in CI 41007796446 (was 4.5). Watch; if CI > 20 min, split heavy imports out of Checked's root or run nanoda per module.

## Open questions for Alexander
None. F3 sent as information (any contact with authors is his call, 47.1).

## Exact next step
1. Read CI 41019261348 (promotion dac809b) and the records commit's CI by ID; if red, fix before anything else.
2. Hub screen: Bamba, Capozziello, Nojiri, Odintsov, arXiv:1205.3421, cosmography sections (10–11; pp. ~105–115): typeset route, transcribe every coefficient formula (q, j, s, l in terms of H derivatives Eqs. ~(10.x); D_z, R_D, d_L, d_A series; ΛCDM/wCDM/CPL cosmographic parameters; f(R) relations), check each with sympy against an independent derivation. Already known there: F2 (Eq. 11.38), F3 (Eq. 10.25), R⁵_D l₀ term. Record new hits as candidates (FINDINGS table), typeset-confirmed.
3. C1 (Cattoën–Visser 2007 Eq. 59, d_Q y² coefficient 1/12 vs 1/24 — see FINDINGS row): reuse `CCS.inversion` pattern: build d_Q(y) as a series via Taylor of a, χ = ∫dt/a, y = z/(1+z); prove the general coefficient, refute the printed one.
4. Optional Lean: R⁵_D (CCS 2008 A5) via χ(x) = ∫₀ˣ dx'/A(x') + o(x⁶).
Blocking: nothing.
