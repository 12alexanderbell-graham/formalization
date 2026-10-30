# STATE

Last updated: 2026-10-30, run 2026-10-30T1628Z (scheduled).

## Phase
S1, S2 DONE. Working target 1 (cosmography). Verified findings F1–F11.

## Target 1: Cosmography: low-redshift (Hubble-series) expansions in FLRW
Case and the eight items: `TARGETS.md` #1 (unchanged).
Bottleneck now: source supply beyond the Bamba hub. Run 1628Z opened the GRB/quasar cosmography family (F11 from Demianski 2017 / Lusso 2019; the log-polynomial relations behind the > 4σ tension are correct). The CDL 2019 review (1904.01427) screen (end of run 1628Z) gave C19–C23, two of which change reported numbers: work those next. Negative branch: if two more hubs come back clean, the misprint-hunting yield is exhausted and target 1 should move to a settled-question result (convergence/truncation of cosmographic series, TARGETS #1 hidden-assumption angle).

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
- **PROVED** (F10) `Checked.Cosmography.FREta.eta_ratios`, `eta20_hasDerivAt`, `eta30_hasDerivAt`, `printedEta20_false_at`, `printedEta30_false_at`, `printedEta20Claim_false`, `printedEta30Claim_false`, `eta_numbers`. Audit `runs/2026-10-30T1628Z/audit.md`. Promotion f258555, CI 41093965309 green (incl. nanoda).
- **PROVED** (F11) `Checked.Cosmography.DemianskiZ.flat_corrections`, `demDL4_fails_past`, `demDA4_fails_past`, `demDLzClaim[Past]_false`, `demDAzClaim[Past]_false`. Audit `runs/2026-10-30T1628Z/audit_c15.md`. Promotion 21729d5, CI 41096316923 green (incl. nanoda).
- **Findings F1–F11** (FINDINGS.md): all verified and reported to Alexander (F10, F11 this run).
- C8 one route. C10 (R⁴_D, R⁵_D): two routes (referees 1028Z, 1232Z). C12: two routes, misprint, not formalized. C11, C13 → F9; C14 → F10; C15, C16 → F11. C17, C18 (screen 1628Z): one route, presentational. C19–C23 (screen2 1628Z, CDL 2019 review 1904.01427): one route each; C19, C20 change reported numbers.

## Environment (this run)
- Repo pre-cloned shallow (add_repo not exposed; not needed); unshallowed, stale local main reset to origin/main. Pushes verified (remote head = local each time).
- Local Lean: elan + `lake exe cache get`; new files elaborate in < 10 s; `lake build Work` (all) exceeds 2 min locally — build named modules.
- CI (read by ID): previous run's last 41082158609 green; LOCK 41090422641, C14 freeze 41091234687, proofs 41093221867, blind closure 41093819830, C14 promotion 41093965309 (checked job incl. nanoda 6.3 min, no-sorry) all green. C15/C16 freeze 41094514730, proofs 41096213672, promotion 41096316923 (both jobs incl. nanoda): all green. Records/LOCK-removal commit: read next run.

## Daily review (53.3), 2026-10-30
- AUDITED + PROVED headlines in last 24 h: 2 (0028Z) + 5 (0220Z) + 5 (0430Z) + 5 (0628Z) + 9 (0828Z) + 12 + 6 (1028Z) + 10 (1232Z) + 8 (1428Z) + 8 + 7 (1628Z). Findings: F1–F11 verified.
- Bottleneck history: candidate supply (0628Z) answered by hub screening; curvature tooling (1028Z–1232Z); F(R) machinery (1428Z). Run 1628Z: new source families (GRB/quasar cosmography → F11; CDL 2019 review → C19–C23).
- Patterns fixed run 1428Z: HasDerivAt combinator shape (PROMPT note); differentiate-eventual-identity pattern recorded. 1232Z experiments evaluated: keep.
- Honest check: F1–F9 are formula misprints in one hub and its upstream papers; numbers in those papers were mostly unaffected. The checked general theorems (cosmographic series, F(R) closure) are the durable value. Next: aim at results people compute with (TARGETS.md).

## Known gaps
- Cosmetic linter warnings in generated proofs. Leave.
- nanoda step ~6.5 min in CI 41034616298, 8.2 min in 41066721346 (checked job 15 min total). Watch; if CI > 20 min, split heavy imports or run nanoda per module.
- F4's Lean result is the flat instance; its curved sign error now follows from F6's general theorem (corrected D² is part of `lumDist_y_fifth_order`), but no separate curved refutation of the printed D² is stated. F5 flat only.

- F9: the printed F″, F‴ relations (11.23)–(11.24) (with the printed R) are not refuted in Lean: both sides vanish in ΛCDM; a model with F″(R₀) ≠ 0 would be needed (ODE existence for a given F).
- F10: existence of F(R) models on the ε-family for ε ≠ 0 is not shown (paper does not claim it); the ε-range defect at Ω = 0.041 (pole at ε ≈ 0.032) is sympy only.
- F11: whether Demianski et al.'s joint fits used the printed D⁴_A/D⁴_L (effect on q₀, j₀) cannot be settled from the paper.

## Open questions for Alexander
None. F10, F11 sent as information (any contact with authors is his call, 47.1).

## Exact next step
1. Read CI of this run's last commits by ID (C15/C16 runs above if still pending; records/LOCK-removal commit).
1b. **Big track B1** (`TARGETS.md`; Alexander 2026-10-30: "the real goal is big, don't lose it"; PROMPT standing instruction 9): this or the next run spends its main block on B1's first milestone: freeze the statement (exact paper definitions of the log-polynomial and μ), then certified enclosures of the ΛCDM comoving integral in Lean. C19 below is capped at half a run.
2. C19 first (why: printed H(z) z³ sign error that feeds the paper's f(T) reconstruction and fit numbers (262), Figs. 30–35 — the first candidate whose error changes reported results): typeset check of (246) and upstream 1706.02962 (26) yourself (crops in `runs/2026-10-30T1628Z/screen2/`); Lean: H/H₀ = 1 + E₁z + E₂z² + E₃z³ + o(z³) for every C⁴ scale factor (corollary of the lookback series or direct via `littleO_of_hasDerivAt`), then printed E₃ fails whenever its sign matters (EdS a = t^{2/3}, or every model with −3q₀²−3q₀³+j₀(3+4q₀)+s₀ ≠ 0). Freeze; blind + referee + next screen (e.g. 1706.02962 in full, or Benetti & Capozziello 2019 1910.09975) in one message. Then C21 (via `FRCosmo`; read what (211) assumes about F″Ṙ at t₀) and C20.
3. C10, C17, C18, C22, C23 are presentational: parked (PROMPT instruction 9), Lean only if under a third of a run.
4. If two hubs come back clean: plan the settled-question track (convergence radius / truncation error of the z-series vs y-series in flat ΛCDM, TARGETS #1) and tell Alexander (target-direction change, 42.4).
Blocking: nothing.
