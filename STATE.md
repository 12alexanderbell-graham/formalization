# STATE

Last updated: 2026-10-30, run 2026-10-30T1828Z (scheduled; Alexander joined live).

## Phase
GOAL (annex 36.0, Alexander 2026-10-30, verbatim in PROMPT instruction 9): a system that lets scientists trust AI-produced science without outside verification. Physics (target 1, cosmography; F1–F11; B1) is the proving ground. Active: **Trust track T1, definition fidelity** (`TARGETS.md`).

## Trust track status
- **T1 definition fidelity** (`Work/Fidelity/`, Work only, CI-built, standard axioms, no sorry):
  - Specs: `LumDistSpec` (anchors), `LumDistSpec2` (anchors + Etherington), `HubbleSpec`, `DecelSpec`, `AngDistSpec`, `FlatLCDMSpec`. All met by the program's definitions (`*_meets_spec*`).
  - **Pinning** (any function meeting the spec = the definition on the physical domain): `lumDistSpec2_pins`, `hubbleSpec_pins` (LumDistSpec2.lean), `Gaps.decelSpec_pins`, `Gaps.angDistSpec_pins` (SpecGaps.lean). Not pinned: `FlatLCDMSpec` (the model hypothesis behind F1), `LumDistSpec` (anchors only; 4 gaps proved in SpecGaps.lean).
  - Metric (`python3 scripts/fidelity_killrate.py`): blind mutants 30/30 refuted in Lean (2 excluded as equal on the physical domain), author mutants 10/10; spec gaps found by a spec-aware adversary: 4 (all in anchors-only `LumDistSpec`, all closed by `LumDistSpec2`).
  - Protocol that produced honest numbers: spec writer and red team are separate subagents blind to each other; freeze both before refuting; then a spec-aware adversary searches for wrong definitions that pass; close gaps with general laws + a pinning theorem.
- T2–T5: not started (TARGETS.md).

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
- Repo pre-cloned; local main fast-forwarded; pushes verified (remote head = local each time).
- Local Lean: elan + `lake exe cache get` (~3 min); build Checked deps by module.
- CI (read by ID): 41107164729 (LOCK), 41107875967 (goal records), 41109420256 (LumDistSpec + blind 12) green. 41111474000 (freeze b68bff5), 41112096428 (RedTeamMoreCheck), 41113310308 (SpecGaps, LumDistSpec2) were in progress at record time: read next run. Records/LOCK-removal commit: read next run.

## Daily review (53.3), 2026-10-30
- Earlier today: F1–F11 verified findings, many AUDITED + PROVED headlines (see CHANGELOG).
- Alexander's correction (1828Z): the product is the trust system. Honest check against it: until this run, fidelity (the step a scientist cannot check from the kernel) rested on prose and same-model subagents. Now 4 of the 5 central definitions are pinned by machine-checked specs, and there is a metric. Are we closer to AI science trustworthy without outside checking? Yes for definition fidelity of these 5; no progress yet on statement fidelity (T2), transcription (T3), numerics (T4), or a pipeline false-acceptance rate (T5).

## Known gaps
- Cosmetic linter warnings in generated proofs. Leave.
- nanoda step ~6.5 min in CI 41034616298, 8.2 min in 41066721346 (checked job 15 min total). Watch; if CI > 20 min, split heavy imports or run nanoda per module.
- F4's Lean result is the flat instance; its curved sign error now follows from F6's general theorem (corrected D² is part of `lumDist_y_fifth_order`), but no separate curved refutation of the printed D² is stated. F5 flat only.

- F9: the printed F″, F‴ relations (11.23)–(11.24) (with the printed R) are not refuted in Lean: both sides vanish in ΛCDM; a model with F″(R₀) ≠ 0 would be needed (ODE existence for a given F).
- F10: existence of F(R) models on the ε-family for ε ≠ 0 is not shown (paper does not claim it); the ε-range defect at Ω = 0.041 (pole at ε ≈ 0.032) is sympy only.
- F11: whether Demianski et al.'s joint fits used the printed D⁴_A/D⁴_L (effect on q₀, j₀) cannot be settled from the paper.

- T1: specs and pins are in Work, not Checked (not yet audited for promotion). All agents (spec writer, red team, adversary) are the same model: correlated misconceptions in the laws are not excluded; anchors from closed forms are the independent cross-check.
- T1: `AngDistSpec`'s flat/closed/open laws are near-restatements of the definition; their independence is the blind authorship plus the anchors.

## Open questions for Alexander
None.

## Exact next step
1. Read CI 41111474000, 41112096428, 41113310308 and the records commit by ID; fix anything red first.
2. **T1, close the last gap:** spec-aware adversary on `FlatLCDMSpec` (the model hypothesis behind F1). Then either prove `flatLCDMSpec_pins` (expected route: add the law "P Ω a t₀ ↔ H₀ > 0 ∧ eventually a > 0, differentiable and H² = H₀²(Ω(1+z)³ + 1 − Ω)", cross-checked by the existing anchors) or record the gaps.
3. **T1 → Checked:** promote the specs and pinning theorems (`Checked/Fidelity/…`, specific imports, fidelity audit of the laws: each law matched to a textbook equation by a referee subagent who sees only the spec). Then CI makes "definition is pinned" part of the judge, and TRUSTED_DEFINITIONS rows cite the pin theorem instead of prose.
4. **T1 generalization:** add a CI check that every `def` in `Checked/` used by a headline either has a pinning spec or is listed as unpinned with a reason (report-only first, LIV).
5. Then T2 (statement fidelity, machine checks: non-vacuity witness per Checked headline, hypothesis-drop mutation) — the next weakest link.
Why: these make "the definition means the physics" a kernel-checked fact for everything the findings rest on. Blocking: nothing.
