# STATE

Last updated: 2026-10-30, run 2026-10-30T2228Z (scheduled).

## Phase
GOAL (annex 36.0, PROMPT instruction 9): a system that lets scientists trust AI-produced science without outside verification. Physics (target 1, cosmography; F1–F11; B1) is the proving ground. Active: **Trust track T2 (statement fidelity) and T3 (transcription fidelity)** (`TARGETS.md`); T1 closed (all headlines on pinned definitions, CI-enforced). Measured by the trust map.

## Trust track status
- **Trust map** (`TRUST_MAP.md`, generated and enforced by `scripts/trust/StatementDeps.lean` in CI). Three machine-checked metrics (run 2228Z):
  - **T1:** 101/101 headlines rest only on pinned definitions (19 pins; `transverse` pinned by blind ODE law, `transverseSpec_pins`; `dQFlat` reclassified PRINTED: source convention). **Blocking** since 2228Z: a headline on an unpinned PHYSICS/UNCLASSIFIED definition fails CI.
  - **T2a non-vacuity:** 62/62 conditional headlines have a witness of `nonvacuity% h` (obligation computed from the statement: `Checked/Trust/NonVacuity.lean`; witnesses `Checked/Trust/Witnesses.lean`). **Blocking.** Adversarial review fixed 7 holes (`runs/2026-10-30T2228Z/nv_adversary.md`). Every pin's spec is thereby proved satisfiable.
  - **T3 second reading:** 36/38 PRINTED definitions have a machine-checked agreement with a blind second transcription (`Checked/Trust/SecondReading.lean`, `Transcriptions.lean`; marked ² in the map). Informational. Second batch (F(R) `P0…Q3`, `printedR`, η `qL/sL/lL`, `printed20/30/Den`) agrees too (`SecondReadingFR.lean`, `TranscriptionsFR.lean`); the second reader reproduced the paper's η numbers (11.44)–(11.45) and, by its own sympy check, re-found the F9/F10 inconsistencies (printed R; ε-coefficients not the expansion of the printed formulas). Not yet read twice: `dQFlat` (Eq. 5), `jL` (= 1), and the printed parts inside the F1/F2 CLAIM definitions.
- Mutation benchmark (`python3 scripts/fidelity_killrate.py`): blind 30/30, author 10/10.
- Controls: `control/bad-pin-registry` (2028Z) and `control/vacuous-headline` (CI 41140145749) FAILED as required at the trust-map step; `control/unpinned-and-hidden` CI 41142047810 FAILED as required with both errors.
- T4, T5: not started.

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
- Repo pre-cloned; main fast-forwarded; pushes verified (remote head = local each time). Local Lean: elan + cache (~4 min); `lake build Checked` incremental ~1–3 min; `StatementDeps.lean` ~1:50 locally (was 45 s; the non-vacuity pass).
- CI (read by ID): 41138309671 (LOCK) green, 41139919276 (non-vacuity v1) green; control 41140145749 FAILED as required ("no non-vacuity witness" for the vacuous headline; decoy rejected). 41141815326 (T1 close, hardened generator) green. Control 2 41142047810 FAILED as required with both errors (`uses_unpinned … fakeDist`; `hidden_vacuous: no non-vacuity witness`). 41142867442 (T3 batch 1), 41142998164 (records), 41143675338 (T3 batch 2) green: the non-vacuity, pin and second-reading checks are PROVED-level (CI green, standard axioms). Final records commit: read next run.

## Daily review (53.3), 2026-10-30
- 22:28Z run: statement fidelity and transcription fidelity became machine-checked (non-vacuity 62/62 enforced; second reading 36/38); T1 closed and enforced (101/101).
- Is AI-produced science here more trustworthy without outside checking than this morning? Yes, by a machine-computed measure: 77 of 82 physics headlines now rest only on definitions pinned by blind textbook laws (none this morning; ≤ 15 at 20:28Z), and the dependency map itself is CI-generated. Not yet: statement fidelity (T2), transcription (T3), numerics (T4), pipeline false-acceptance rate (T5).

## Known gaps
- Cosmetic linter warnings in generated proofs. Leave.
- nanoda step ~6.5 min in CI 41034616298, 8.2 min in 41066721346 (checked job 15 min total). Watch; if CI > 20 min, split heavy imports or run nanoda per module.
- F4's Lean result is the flat instance; its curved sign error now follows from F6's general theorem (corrected D² is part of `lumDist_y_fifth_order`), but no separate curved refutation of the printed D² is stated. F5 flat only.

- F9: the printed F″, F‴ relations (11.23)–(11.24) (with the printed R) are not refuted in Lean: both sides vanish in ΛCDM; a model with F″(R₀) ≠ 0 would be needed (ODE existence for a given F).
- F10: existence of F(R) models on the ε-family for ε ≠ 0 is not shown (paper does not claim it); the ε-range defect at Ω = 0.041 (pole at ε ≈ 0.032) is sympy only.
- F11: whether Demianski et al.'s joint fits used the printed D⁴_A/D⁴_L (effect on q₀, j₀) cannot be settled from the paper.

- T1: all spec writers, referees and provers are the same model: correlated misconceptions in the laws are not excluded; closed-form anchors are the independent cross-check. `LumDistSpec`, `FlatLCDMSpec` (anchors only) kept for the record.
- T1: `RedshiftSpecCore`/`CosmoCoeffSpecCore` omit 3+3 blind fields not yet proved for the definitions (`deriv_emission`, `deriv_observation`, `low_z`; `decel_hubble`, `recursion`, `time_scale`); the pins do not use them.
- Trust map: `def_kinds.txt` is hand-classified; only `Checked` definitions are walked (Mathlib trusted).
- T2a: non-vacuity = one instance satisfies all hypotheses; not typicality, not necessity of each hypothesis. Witness instances are mostly de Sitter (a = eᵗ). The obligation generator unfolds only `Checked` definitions.
- T3: second readings are by the same model (independent reading of the same images); CCS 2008 Eq. (A2) exists only in arXiv v2 (docstrings cite v1/v2 crops); Demianski (23) double minus at a line break read as −210q₀j₀ by both readings.
- T1: `AngDistSpec`'s flat/closed/open laws are near-restatements of the definition; their independence is the blind authorship plus the anchors.

## Open questions for Alexander
None.

## Exact next step
0. **Read PROMPT instruction 10 and `TARGETS.md` "THE RESULT" first** (Alexander, 2026-10-31): the work is the full goal, demonstrated and published. Choose each run's block by which of its five parts it moves most; the items below are the immediate queue, not the ambition.
1. Read the CI runs listed under Environment that are not yet confirmed green. Fix anything red first.
2. T3: second-read `dQFlat` (Eq. 5) and the printed formulas inside the F1/F2 CLAIM definitions (Aviles Eq. 15 l₀/m₀, CLS Eq. 22 l₀): factor them out as PRINTED defs first. Then make "PRINTED without second reading" blocking.
3. T2b hypothesis necessity: for each headline hypothesis, either a Checked counterexample (other hypotheses hold, conclusion fails) or a registry entry DOMAIN with reason; start with the refutations' nondegeneracy hypotheses (`decel ≠ 0`, `K ≠ 0`, …), where the counterexample is the model making the printed and correct coefficients coincide.
4. T5 (pipeline false-acceptance rate): seed wrong claims of each kind the checks target (vacuous, unpinned, mis-transcribed, wrong definition) on control branches and record which the CI catches; a mis-transcription is not caught by CI today unless it is among the 23 second-read.
Blocking: nothing.
