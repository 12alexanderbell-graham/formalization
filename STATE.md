# STATE

Last updated: 2026-10-31, run 2026-10-31T0028Z (scheduled).

## Phase
GOAL (annex 36.0, PROMPT instruction 9): a system that lets scientists trust AI-produced science without outside verification. Physics (target 1, cosmography; F1–F11; B1) is the proving ground. Active: **Trust track T5 (measured false-acceptance rate), T2, T3** (`TARGETS.md`, "THE RESULT" part 3); T1 closed (all headlines on pinned definitions, CI-enforced). Measured by the trust map and the T5 benchmark (`runs/2026-10-31T0028Z/t5/`).

## Trust track status
- **Trust map** (`TRUST_MAP.md`, generated and enforced by `scripts/trust/StatementDeps.lean` in CI). Three machine-checked metrics (run 2228Z):
  - **T1:** 101/101 headlines rest only on pinned definitions (19 pins; `transverse` pinned by blind ODE law, `transverseSpec_pins`; `dQFlat` reclassified PRINTED: source convention). **Blocking** since 2228Z: a headline on an unpinned PHYSICS/UNCLASSIFIED definition fails CI.
  - **T2a non-vacuity:** 62/62 conditional headlines have a witness of `nonvacuity% h` (obligation computed from the statement: `Checked/Trust/NonVacuity.lean`; witnesses `Checked/Trust/Witnesses.lean`). **Blocking.** Adversarial review fixed 7 holes (`runs/2026-10-30T2228Z/nv_adversary.md`). Every pin's spec is thereby proved satisfiable.
  - **T3 second reading:** 36/38 PRINTED definitions have a machine-checked agreement with a blind second transcription (`Checked/Trust/SecondReading.lean`, `Transcriptions.lean`; marked ² in the map). Informational. Second batch (F(R) `P0…Q3`, `printedR`, η `qL/sL/lL`, `printed20/30/Den`) agrees too (`SecondReadingFR.lean`, `TranscriptionsFR.lean`); the second reader reproduced the paper's η numbers (11.44)–(11.45) and, by its own sympy check, re-found the F9/F10 inconsistencies (printed R; ε-coefficients not the expansion of the printed formulas). Not yet read twice: `dQFlat` (Eq. 5), `jL` (= 1), and the printed parts inside the F1/F2 CLAIM definitions.
- Mutation benchmark (`python3 scripts/fidelity_killrate.py`): blind 30/30, author 10/10.
- Controls: `control/bad-pin-registry` (2028Z) and `control/vacuous-headline` (CI 41140145749) FAILED as required at the trust-map step; `control/unpinned-and-hidden` CI 41142047810 FAILED as required with both errors.
- **T5 false acceptance (run 0028Z, first measurement):** red teams of a different model (Sonnet) seeded 24 defects (A honest, B adversarial, C adversarial vs the new checks; `runs/2026-10-31T0028Z/t5/`). **Checks as of 2228Z accepted 15 of 15 valid A+B defects** (one INVALID: missing import). After this run's strengthening: **6 of 15 accepted** (caught: everything that changes frozen content or cites unregistered results; accepted: new wrong definitions labelled FORMULA, wrong numbers and scope in prose, an existential headline). Red team C (aimed at the new checks, judged against v3): 2/8 accepted (C02 decorative spec in a pin, addressed by v4, not re-judged; C06 conjunction-bundled hypothesis, open); 8/8 accepted by the 2228Z checks. **All 23 valid defects passed the local replica of the 2228Z checks; 8/23 pass the checks now on main.** Correction: the local judge does not build `Work`; CI does, and the control run 41158182668 (B02) failed in CI at the Work build (an audit file uses the old statement), so the before-counts are upper bounds. Table: `runs/2026-10-31T0028Z/README.md`.
- **New blocking checks (run 0028Z; LEDGER integrity event):** frozen registry `scripts/trust/frozen.txt` (239 fingerprints: headline and pin statements; definition statement + body + kind; a change needs relock + a LEDGER line naming it, `check_relock.py`); unused binders in headlines and pins (T2b level 0; baseline 0); pins must use an independent SPEC definition; theorems cited in STATE/FINDINGS must be registered headlines (or pure mathematics); Checked may not import Work; private definitions reported; stale TRUST_MAP.md fails.
- T4: not started.

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
- Repo pre-cloned (add_repo not exposed; not needed); main fast-forwarded; a chat session pushed 7ad9dc3 (Alexander's instruction 10) at 00:29Z, LOCK rebased on it. Local Lean: elan + cache (~4 min), `lake build Checked` ~3 min from scratch. Previous run's final CI 41145491684 green (all 2228Z runs confirmed green).
- Development in a second worktree (`../fz2`, symlinked `.lake/packages`) because the T5 judge resets the main tree after every defect.
- This run's CI: 41156834643 (T5 checks + records) green, incl. the frozen registry (fingerprints match CI). v4 push (023b5b4) and final records: read next run. Control `control/frozen-weakened` 41158182668 FAILED, but earlier than intended: at the Work build in the axiom-audit step (`Work/Cosmography/LookbackAudit.lean` uses the old statement), so check_relock is not yet shown to bite in CI.

## Daily review (53.3), 2026-10-31
- 00:28Z run (first of the day): the first measurement of the system as a whole. The pipeline that the trust metrics described as machine-checking every link accepted every valid seeded wrong claim (15/15) from a different model's red teams; the strengthened checks catch the classes that change *existing* checked content (statements, transcriptions, pins, classifications) or cite unregistered results, and not yet new wrong definitions dressed as formulas, wrong numbers in prose, existential or partly used hypotheses.
- Is AI-produced science here more trustworthy without outside checking than yesterday, and by what measure? Yes: false acceptance on the A+B benchmark fell from 15/15 to 6/15, and the number now exists. Experiment check (Alexander 2026-10-31, no narrowing): this run's plan and records state the full goal (THE RESULT) and its next decisive step; no reduced scope recorded.

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
- **T5 open holes (accepted by the strengthened checks; `runs/2026-10-31T0028Z/README.md`):** a *new* wrong definition classified FORMULA/COMPOSITE (A04, B04: kinds are hand-assigned; only PHYSICS needs a pin); wrong numbers and overstated prose in STATE/FINDINGS (A03, A06, B07, the STATE half of B05: records are not generated from Lean); an existential headline read as universal (A05); C-round holes (see run README). A LEDGER line naming a changed frozen constant passes `check_relock.py`: the guard is disclosure, not prevention.

## Open questions for Alexander
None.

## Exact next step
0. **Read PROMPT instruction 10 and `TARGETS.md` "THE RESULT" first** (Alexander, 2026-10-31): the work is the full goal, demonstrated and published. Choose each run's block by which of its five parts it moves most; the items below are the immediate queue, not the ambition.
1. Read this run's CI by ID (first push of the frozen registry: if `frozen.txt` fingerprints differ in CI from local, the hashes are not portable: switch `fingerprint` to a hash of the pretty-printed statement and relock). Fix anything red first.
2. T5: add `lake build Work` to the judge (CI builds Work) and re-judge all 23 defects; push a control that reaches check_relock (change a frozen entry not used in Work, relock, no LEDGER); confirm the reasons for C04, C05 (rerun with the fixed harness filter, which now saves the full log) and judge C02 against v4; then close the C holes that are mechanical (bundled conjunctions: split ∧ hypotheses before the unused check; pins: require a hypothesis `Spec D` with `D` a bound variable used by the proof) and rerun A, B, C. Then a fresh red team D (different model) against the new version: the benchmark grows, the accepted fraction must fall.
3. T5 open classes need new mechanisms, not patches: (a) FORMULA/COMPOSITE dodge: a definition whose docstring or name claims a physical quantity must be PHYSICS (or be proved equal to a pinned PHYSICS definition in the stated model, e.g. `lumDistEdS = lumDist` in EdS); (b) records: generate the Results and FINDINGS numbers from Lean (a script that prints each headline's statement and each certified interval) so prose cannot overstate; (c) existential headlines: flag `∃`-conclusions in the map.
4. T3: second-read `dQFlat` (Eq. 5) and the printed formulas inside the F1/F2 CLAIM definitions; then make "PRINTED without second reading" blocking and forbid numeric literals in CLAIM bodies (all printed numbers in PRINTED definitions).
Blocking: nothing.
