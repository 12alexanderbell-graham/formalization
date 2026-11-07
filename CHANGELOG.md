# CHANGELOG (append-only, one entry per run)

## 2026-10-30, setup (chat session)
- Created the repository layout, governance files, Lean skeleton and CI workflow.
- Reassembled Alexander's original constitution from five uploaded parts; SHA-256 4a34f9846fafce3b5d760d4b1dcec37eebe21247604666d48eb0a7ae86bc394e matches the hash in his v2.0 file.
- CI never run yet. Local Lean install refused by the environment.
- CI judge set up and proven: green on main (run 40967111191); positive controls on `control/sorry-in-checked` and `control/axiom-in-checked` failed as required, both caught by axiom-audit. nanoda report-only (format mismatch). S1 done.
- Scheduled task "Formalization run" created: every 2 hours (12 runs a day), cloud only.

## 2026-10-30T0028Z (scheduled run)
- Env: repo ok; local Lean installed via elan (works); CI runs 40981530819, 40982411889 green.
- S2 done: TARGETS.md built (8 candidates); target 1 = cosmographic expansions.
- PROVED + AUDITED: `Checked.Cosmography.lookback_second_order` (o(z²)) and `..._bigO` (O(z³)); blind restatement derived verbatim.
- Literature screen: 4 candidate coefficient errors (unverified) in FINDINGS.md.
- Message to Alexander: target pick (L.2).

## 2026-10-30T0220Z (scheduled run)
- Env: repo ok; local Lean via elan ok; local build of lean4export/nanoda refused by the environment (used CI). CI runs 40994124990, 40995247069, 40996176398, 40996270496 green; later runs in STATE.
- Typeset verification of C1–C4: all four confirmed as printed (rendered PDFs).
- **First verified finding F1** (Aviles et al. 2012 Eq. 15, ΛCDM l₀/m₀ misprint, repeated in a 2014 paper; the papers' numbers are unaffected). PROVED + AUDITED in Checked: general flat ΛCDM coefficients q₀…m₀ and refutations of the printed l₀ (every Ω ∈ (0,1] ) and m₀. Blind restatement derived; referee STANDS-WITH-CORRECTIONS.
- nanoda repaired (pinned lean4export v4.35.0 + nanoda_lib master) and made blocking again.
- PROMPT.md: Alexander's no-approval instruction; typeset route; proof-generation note.
- Message to Alexander: verified finding F1 (L.2).

## 2026-10-30T0430Z (scheduled run)
- Env: repo ok (session repo pre-cloned; add_repo tool not exposed, not needed); local Lean via elan ok; CI runs 41003668913, 41006086049, 41007266062, 41007523313, 41007796446 green (both with nanoda blocking).
- **Second verified finding F2** (CLS 2011 Eq. 22, CPL l₀ missing factor 9; reprinted in Bamba et al. 2012). PROVED + AUDITED in Checked: general flat matter + CPL q₀…l₀ for every Ω, w₀, wₐ; printed l₀ refuted (explicit model, and at every parameter point with (1−Ω)(7−Ω)wₐ ≠ 0 via ODE existence). Blind restatement closed in Lean; referee STANDS-WITH-CORRECTIONS.
- New reusable tool: `exists_local_model` (local model for any smooth expansion law).
- PROMPT working notes: witness by ODE existence; auxiliary-function method.
- Message to Alexander: verified finding F2 (L.2).

## 2026-10-30T0628Z (scheduled run)
- Env: repo ok (pre-cloned; add_repo tool not exposed, not needed); local Lean via elan ok; CI runs 41014293442, 41015036651, 41016090351, 41016197447, 41016220832 green; promotion CI in STATE.
- **Third verified finding F3** (Capozziello, Cardone, Salzano 2008 Eq. A2: lookback-distance z⁵ coefficient, 7/2 q₀⁴ should be 7/8 q₀⁴; reprinted in three later papers incl. the Bamba et al. 2012 review). PROVED + AUDITED in Checked: general fifth-order lookback series for every C⁵ scale factor; printed D⁴ refuted in every model with q₀ ≠ 0 (two-sided and past-only). Blind restatement closed in Lean; referee STANDS.
- New reusable tool: asymptotic series inversion (`Checked.Cosmography.CCS.inversion`).
- PROMPT working notes: series inversion method; hub screening; records quote FINDINGS; commit attribution.
- Message to Alexander: verified finding F3 (L.2).
- Hub screen of Bamba et al. 2012 Sec. 10: candidates C5–C8 (C5 sign error confirmed by a second route; upstream source correct). CI 41019261348 (promotion) green.

## 2026-10-30T0828Z (scheduled run)
- Env: repo ok (pre-cloned); local Lean via elan ok; CI runs 41026700321, 41027239565, 41032795335, 41034616298, 41034875158, 41035264438, 41036122533 green (F4 and F5 promotions incl. nanoda).
- **Verified finding F4** (Bamba et al. 2012 review Eq. 10.54: sign of the y-redshift d_L coefficient D²_{L,y}; upstream correct; review's own d_A,y contradicts it). **Verified finding F5** (Cattoën–Visser 2007 Eq. 59, also gr-qc/0703122 and 0809.0537 Eq. 32: d_Q(y) y² prefactor 1/12 → 1/24). PROVED + AUDITED in Checked: general flat d_L(y) and d_Q(y) to third order (d_L from the comoving integral), refutations of the printed coefficients. Blind restatements closed in Lean; referees STANDS-WITH-CORRECTIONS. C6, C7 confirmed by a second route.
- New tools: `littleO_of_hasDerivAt` (MVT: integrals, real powers), `rpow_expansion`; Work helper `transverse_expansion` (curved S_K to χ⁵, every K) for C6/C7.
- PROMPT notes: MVT method; heartbeat trap; referee as second route. LEDGER: 0628Z experiments evaluated (keep).
- Message to Alexander: F4, F5 (L.2).

## 2026-10-30T1028Z (scheduled run)
- Env: repo ok (pre-cloned); local Lean via elan ok; previous CI 41036605782, 41037683712 green; CI 41048210895 (C6 promotion), 41051129131 (C7 promotion) green; others in STATE.
- **Verified finding F6** (Bamba et al. 2012 Eqs. 10.55–10.57, verbatim from Capozziello & Salzano 2009 Eqs. 56–58: curvature terms of D³_{L,y}, D⁴_{L,y} wrong; flat parts right). PROVED + AUDITED in Checked: general curved d_L(y) to y⁵ for every real K and every C⁵ scale factor; refutations (general conditions, a = eᵗ with K = 1, Milne). Blind restatement closed in Lean; referee STANDS-WITH-CORRECTIONS.
- F4 provenance corrected (sign error already in 0902.0088 Eq. 55). New candidates C9, C10 (referee side checks); C7 third route.
- New tool: truncated-series algebra (`approx_mul`, `approx_pow`). PROMPT notes: approx algebra; `unfold` order; referee file hygiene.
- **Verified finding F7** (same review Eqs. 10.61–10.63, from 0902.0088 Eqs. 62–64: curvature terms of D³_{A,y}, D⁴_{A,y} wrong). PROVED + AUDITED in Checked as a corollary (d_A = d_L/(1+z)²); blind closed in Lean; referee STANDS.
- Message to Alexander: F6, F7 (L.2).

## 2026-10-30T1232Z (scheduled run)
- Env: repo ok (pre-cloned; stale local main reset to origin); local Lean via elan ok; previous CI 41052780695 green; promotion CI 41066721346 green (incl. nanoda); others in STATE.
- **Verified finding F8** (Bamba et al. 2012 Eqs. 10.43–10.44, 10.50–10.51, from Capozziello & Salzano 2009: z-series D⁴_L, D⁴_A miss +k²/120; truncation inherited from Visser 2004; minor). PROVED + AUDITED in Checked: general curved d_L(z), d_A(z) to z⁵ for every real K; refutations for every K ≠ 0. Blind closed in Lean; referee STANDS-WITH-CORRECTIONS.
- Sec. XI screen: candidates C11–C14 (F(R) cosmography relations, η numbers), F2 reprint traced to 2008. C10 second route.
- PROMPT notes: parallel subagents at freeze; series transfer by exact identities. LEDGER: 1028Z experiments evaluated (keep).
- Message to Alexander: F8 (L.2).

## 2026-10-30T1428Z (scheduled run)
- Env: repo ok (pre-cloned; stale local main reset to origin); local Lean via elan ok; previous CI 41069186273 green; this run: 41071807029, 41073073503, 41078117151, 41078660695, 41079150781, 41079704808 (promotion, incl. nanoda) all green.
- **Verified finding F9** (Bamba et al. 2012 Sec. XI, F(R) cosmography: denominator R of (11.31) wrong — from Capozziello, Cardone, Salzano 2008 Eq. (33), with a further +18/−18 slip — so the printed F(R₀) formula (11.21) fails the paper's own ΛCDM check (11.40); (11.13) sign error). PROVED + AUDITED in Checked: F(R₀), F″(R₀), F‴(R₀) from (q₀, j₀, s₀, l₀) for every model of the metric F(R) FLRW equations (no nondegeneracy); ΛCDM model for every Ω ∈ (0,1); refutations. Three independent derivations agree; blind closed in Lean; referee STANDS.
- C12, C14 second routes. Tools: `hvals`, `curvData`, differentiate-an-eventual-identity pattern.
- PROMPT notes: combinator shape, field-equation differentiation, de Sitter witness. LEDGER: 1232Z experiments evaluated (keep).
- Message to Alexander: F9 (L.2).

## 2026-10-30T1628Z (scheduled run)
- Env: repo ok (pre-cloned, shallow; unshallowed, stale local main reset to origin); local Lean via elan + cache; previous CI 41082158609 green; this run 41090422641, 41091234687, 41093221867, 41093819830, 41093965309 (C14 promotion, incl. nanoda) green; later runs in STATE.
- **Verified finding F10** (C14: Bamba et al. 2012 (11.42)–(11.45), from 0802.1583: first-order F(R)-vs-GR deviations η₂₀, η₃₀ wrong in formula and number; conclusion survives). PROVED + AUDITED in Checked (`FREta`).
- **Verified finding F11** (C15/C16: Demianski et al. 2017 flat D⁴_L −105q₀⁴ and D⁴_A +137j₀; D⁴_L reprinted in Lusso et al. 2019; absorbed by free l₀ in d_L-only fits). PROVED + AUDITED in Checked (`DemianskiZ`).
- New source families screened: log-polynomial quasar cosmography (relations behind the > 4σ tension claims all correct); Capozziello, D'Agostino, Luongo 2019 review → candidates C19–C23 (C19 H(z) z³ sign and C20 G_eff condition change the paper's f(T) reconstruction numbers; one route each).
- PROMPT notes: screen a new hub at every freeze; transcriptions must reproduce printed numbers; build scope; rational identities. LEDGER: 1428Z experiments evaluated.
- Message to Alexander: F10, F11 (L.2).

## 2026-10-30T1828Z (scheduled run; Alexander joined live)
- Env: repo ok (pre-cloned); local Lean via elan + cache; CI 41107164729, 41107875967, 41109420256 green; later runs in STATE.
- Alexander redefined the goal live (annex 36.0, verbatim): a system that lets scientists trust AI science without outside verification. PROMPT instruction 9, core, TARGETS (Trust track T1–T5) rewritten. B1 numbers kept as a demonstration (`runs/2026-10-30T1828Z/b1_numbers.out.txt`).
- **T1 definition fidelity, machine-checked** (`Work/Fidelity/`): specs for lumDist, angDist, hubble, decel, IsFlatLCDM; blind red-team mutants 30/30 refuted in Lean; a spec-aware adversary found 4 gaps in the anchors-only d_L spec; `LumDistSpec2` (Etherington) closes them; pinning theorems for lumDist, angDist, hubble, decel. Metric script `scripts/fidelity_killrate.py`.
- Adversary on `FlatLCDMSpec`: 3 plausible + 1 contrived gaps (Lean-proved), to close next run.
- Referee of the spec laws (all correct); fidelity audit; specs + pins promoted to `Checked/Fidelity/` (43191aa).
- PROMPT: working note on the fidelity protocol; LEDGER experiment.

## 2026-10-30T2028Z (scheduled run)
- Env: repo ok (pre-cloned); local Lean via elan ok; previous CI 41115616706, 41116631712 green; this run's CI in STATE.
- T1: `IsFlatLCDM` pinned by a blind first-principles formulation (`FriedmannLCDM`; `isFlatLCDM_iff_friedmann`, Darboux for the sign of H; `FlatLCDMSpec2`, `flatLCDMSpec2_pins`). Referee STANDS; audited; promotion CI 41125393349 green.
- New trust tool: trust map (`scripts/trust/StatementDeps.lean` → `TRUST_MAP.md`; CI step; negative-control branch `control/bad-pin-registry`). It showed `cosmoCoeff` (67 headlines) and `redshift` (58) unpinned.
- T1: blind specs (frozen) and pins for `redshift` (integral law), `cosmoCoeff` (Taylor law; uniqueness of Taylor coefficients), `yred`, `omega0`, `curvK`, plus `lumDistFlat`, `comoving` through `LumDistSpec2`. Referee: laws STAND (convention notes applied). Audited.
- T1: `IsFlatCPL` pinned against blind `FriedmannCPL` (`isFlatCPL_iff_friedmannCPL`, `flatCPL_pins`); referee STANDS.
- T1: F(R) definitions (`curv`, `rhoM`, `FriedmannEq`, `MasterEq`) pinned against a blind F(R) spec (referee STANDS).
- Metric: physics headlines resting only on pinned definitions 77/82 (start ≤ 15/88); pinned definitions 17 (start 4).
- PROMPT notes: blind-spec → verbatim core → meets → pin-by-general-law protocol; trust map usage. LEDGER: experiment (trust map), evaluation of run 1828Z experiments.

## 2026-10-30T2228Z (scheduled run)
- Env: repo ok (pre-cloned); local Lean via elan ok; previous CI green; CI 41139919276 green, control 41140145749 failed as required; others in STATE.
- **T2a (statement fidelity), machine-checked non-vacuity:** obligation computed from each statement (`Checked/Trust/NonVacuity.lean`), 62/62 conditional headlines witnessed (`Checked/Trust/Witnesses.lean`), CI blocks a missing witness. Adversarial subagent found 7 holes; all fixed in-run.
- **T1 closed:** `transverse` pinned by a blind ODE law (Grönwall uniqueness); `dQFlat` reclassified PRINTED; 101/101 headlines on pinned definitions; unpinned physics definitions now block CI.
- **T3 started:** blind second reading of 36 printed coefficients (two batches); all 36 agree with the program's transcriptions (Lean `ring`).
- LEDGER: two integrity events (CI strengthened), experiment T2a. No message to Alexander (no finding; infrastructure progress only).

## 2026-10-31T0028Z (scheduled run)
- Env: repo ok (pre-cloned); chat-session commit 7ad9dc3 (Alexander: instruction 10, THE RESULT) arrived at 00:29Z, LOCK rebased; local Lean via elan ok; previous CI 41145491684 green.
- **T5 started: first measured false-acceptance rate.** Red teams of a different model (Sonnet) seeded 24 defects (A honest, B adversarial, C adversarial vs new checks); local CI-replica judge. Checks as of 2228Z accepted 15/15 valid A+B defects.
- **Checks strengthened** (blocking; LEDGER integrity event): frozen registry of headline/pin statements and definition bodies+kinds with LEDGER-naming rule; unused binders; pin shape; records citations; no Work imports; private definitions; stale TRUST_MAP. After: 6/15 accepted (A+B); red team C against the new checks: 2/8 accepted (v3); in total 23/23 accepted before, 8/23 after. CI 41156834643 green; control branch `control/frozen-weakened` pushed (must fail at check_relock).
- PROMPT notes: T5 harness and second worktree; frozen relock procedure. TARGETS T5 line. LEDGER: experiment T5, integrity event, evaluation of 2228Z experiment. Daily review 2026-10-31.
- Message to Alexander (L.2: something seriously wrong, now measured): the trust pipeline accepted all seeded wrong claims before this run.
- Correction: control 41158182668 failed at the Work build (not at check_relock): the local judge omitted `lake build Work`, so before-counts are upper bounds; re-judge next run.

## 2026-10-31T0228Z (scheduled run)
- Env: repo ok (pre-cloned); local Lean via elan ok; previous CI green; this run's CI ids in STATE (all main runs green).
- **T4 started: certified numbers.** `Checked/Records/` (`RoundsTo`, 14 registered record headlines, 26 values, mostly stated for every flat ΛCDM/CPL model); every computed decimal in FINDINGS is tagged and checked by CI (`scripts/trust/check_numbers.py`), inputs bound to records, silent changes/demotions blocked. Found and fixed F11's −87 (correct −86).
- Also blocking: invented dotted citations; conjunction hypotheses in headlines/pins (C06).
- **T5:** judge v5 replicates CI exactly (Work build included); red team D (Sonnet, 8 defects vs the number check), two in-run hardenings; control `control/frozen-record` failed at check_relock in CI (41163600735) as required. Table `runs/2026-10-31T0228Z/t5/RESULTS.md`.
- PROMPT notes: certified numbers, judge v5. TARGETS: T4 started. LEDGER: integrity events, records correction, experiment, evaluation of 0028Z.
- No message to Alexander (no new finding; infrastructure progress; the corrected F11 number is a record slip in a reported aside, not a finding change).

## 2026-10-31T0428Z (scheduled run)
- Env: repo ok (pre-cloned); local Lean via elan ok; previous CI 41166670314 green; this run's CI ids in STATE.
- **THE RESULT part 2 started: B1, first certified new-science result.** For every flat ΛCDM model with Ω_m ∈ [0.2, 0.4], the RL19 cubic log-polynomial at the ΛCDM-implied coefficients misses the exact distance modulus by > 0.09 mag (z = 3), > 0.3 mag (z = 7), and its miss grows by > 0.18 mag from z = 3 to z = 7 (H₀- and zero-point-free). PROVED + AUDITED in Checked (`Checked/Cosmography/B1Truncation.lean`), with the bridge from the pinned `lumDistFlat` to the ΛCDM integral and an exact global witness (sinh^{2/3}). Referee STANDS-WITH-CORRECTIONS; blind restatement closed in Lean; three new PRINTED definitions second-read and machine-checked (T3).
- New method: certified Riemann sums with tangent/secant bounds (certificates by script, checked by Lean).
- Source facts for the next step: `runs/2026-10-31T0428Z/rl19_numbers.md`.
- PROMPT notes: certified integrals; part rotation; no ar5iv in any brief. LEDGER: experiment, evaluation status of 0228Z.
- Message to Alexander (L.2, major result): B1 first certified result.

## 2026-10-31T0628Z (scheduled run)
- Env: repo ok (pre-cloned); local Lean via elan ok; previous CI 41174555288 green; this run's CI ids in STATE.
- **THE RESULT part 5 started: chemistry, first certified result outside physics.** For the generalized two-parameter cubic equation of state (vdW, RK/SRK, PR family): closed-form critical conditions, existence and uniqueness of the critical point, and Z_c, Ω_b, Ω_a at every critical point (vdW exact; RK 1/3, 0.08664, 0.42748; PR 0.3074, 0.07780, 0.45724), for every temperature function a(T). PROVED + AUDITED in Checked (`Checked/Chemistry/CubicEOS.lean`); `IsCriticalIsotherm` pinned by a blind derivative-free spec (`Checked/Fidelity/CriticalSpec.lean`); blind restatement closed in Lean; referee STANDS-WITH-CORRECTIONS.
- Screen of 17 chemistry sources: candidates C24, C25 (arXiv:2607.10076v1, RK P_c coefficient 2.5% high; PR Z_c formula missing a factor), C26 (Soave 1972 truncation); two routes for C24/C25.
- PROMPT notes: NV obligation of an iff; freeze with minimal hypotheses; blind spec writer proves its own reference; Checked imports for calculus. LEDGER: new headlines, statement strengthening after freeze, part-rotation evaluation (part 5 moved; part 4 queued next).
- Message to Alexander (L.2, major result): first certified chemistry result.

## 2026-10-31T0828Z (scheduled run)
- Env: repo ok (pre-cloned); local Lean via elan ok; previous CI 41181290751 green; this run's CI ids in STATE.
- **THE RESULT part 4 prepared** (part rotation): pre-registered expert-validation protocol `validation/PROTOCOL.md`, packet generated from the repository by `validation/make_packet.py` (40 genuine items drawn by the protocol's own hash, 8 planted controls, sealed key with hash commitment). Pilot with Sonnet reviewers: planted 8/8 caught, genuine 0 material, 6 minor. Remaining step is Alexander's (send the packet).
- Pilot fixes: 27/125 headlines had no self-contained plain-words claim; docstrings written (statements unchanged) and now required by the new blocking CI job `validation-packet`; `F10_exceptions` docstring corrected; trust map shows each headline's own non-vacuity witness.
- **B1 (part 2):** `Checked.Cosmography.B1Sep.cubic_separation` (a cubic agreeing with exact flat ΛCDM, Ω ∈ [0.2, 0.4], within 0.05 mag at z = 3 and 7 up to an offset lies > 5/4 from the ΛCDM point) and `cubic_direction` (on the side a₂ − a₂^ΛCDM < 7 log₁₀2 (a₃ − a₃^ΛCDM)), frozen, proved, both blind restatements closed in Lean, NV witness, promoted to Checked (PROVED + AUDITED, `Checked.Cosmography.B1Sep.*`); referee STANDS-WITH-CORRECTIONS: the RL19 offset points the other way (FINDINGS candidate C27).
- Message to Alexander (L.2: a decision/action that is his, and a result): packet ready to send; B1 direction.

## 2026-10-31T1028Z (scheduled run)
- Env: repo ok (add_repo not exposed, pre-cloned); local Lean via elan + cache; CI green on every push read (ids in STATE).
- THE RESULT part 3 (T5) + part 1: new blocking check T2c `scripts/trust/check_prose.py` (docstrings, names and statement shape against what the statement reaches; glossary; record conjuncts through pinned/printed definitions); docstrings of headlines and pinned definitions frozen (relock, LEDGER); written-out defining laws back terms (B1's ΛCDM machine-backed). Prose baseline 25 known gaps (shrink-only).
- T5 judge v6: A04, A05, B04 rejected (accepted before); red team E (Sonnet, 8 defects aimed at the new check) judged, table `runs/2026-10-31T1028Z/t5/RESULTS.md`.
- Own records: 8 certified-number records found resting on free formulas (baseline; fix queued).

## 2026-10-31T1228Z (scheduled run; records written by run 2026-11-04T0028Z)
- Froze the vdW Maxwell coexistence statements at T = 0.7 T_c (`Work/Chemistry/Coexistence.lean`, 1432f15: `IsMaxwellCoexistence`, `acentric`, `vdW_coexistence_exists`, `vdW_coexistence_unique`); stopped without further commits or records.

## 2026-10-31T1428Z (scheduled run; records written by run 2026-11-04T0028Z)
- Auditor role, then LOCK takeover: referee STANDS-WITH-CORRECTIONS, blind restatement, blind Maxwell spec, 10 Sonnet mutants, 15-source screen (cbbc473); `vdW_coexistence_unique` PROVED in Work (ea04366: every coexistence state has p_s/P_c ∈ [0.200455, 0.200465]); stopped without records, existence still `sorry`.

## 2026-11-04T0028Z (scheduled run)
- Env: add_repo not exposed; repo pre-cloned; LOCK of run 1428Z taken over (48.4). **Local Lean refused by the environment** (elan installer); all Lean checks by CI (branch pushes). Previous CI 41213570920 green.
- **THE RESULT part 5 (and 1): first certified chemistry computation.** `vdW_coexistence_exists` proved (equal maxima of ψ on liquid and gas windows by continuity of compact suprema + IVT; maximizers interior hence on the isotherm), so with `vdW_coexistence_unique`: the vdW fluid at 0.7 T_c has a Maxwell coexistence state, every one has p_s/P_c = 0.20046 (5 d.p.), and ω = −0.3020 (4 d.p.), for every R, a, b > 0. Axioms standard.
- Fidelity: blind Maxwell spec frozen; `maxwellSpec_pins` from the equal-chemical-potential law; all 10 red-team mutants refuted in Lean; blind restatement (equal Gibbs energy form) closed in Lean.
- CI: author-files step (generated TRUST_MAP / relocked frozen.txt / packet as an artifact) so runs without local Lean can promote (LEDGER integrity event; control byte-identical).
- Promotion to Checked: see run README.

## 2026-11-04, run 0228Z (scheduled)
- Part 2 (B1) by part rotation. Local Lean available again (elan accepted).
- Froze, proved, audited and promoted `Checked.Cosmography.B1Fit.fit_direction` (fit-level direction over the quasar range, Ω ∈ [0, 1]) and `Checked.Cosmography.B1FitRL19.rl19_box_unmatched` (C27: the RL19 contour-centre box matches no flat ΛCDM). Referee STANDS-WITH-CORRECTIONS; blind restatements of both closed in Lean; NV witnesses; blind second reading of RL19 Fig. 3.
- New tool: second-order certified quadrature (`Checked/Cosmography/B1FitTools.lean`), generators `runs/2026-11-04T0228Z/scripts/`.
- Records: run README, STATE, LEDGER (relocks, quadrature experiment, evaluations, split box hypotheses), BLUEPRINT, TARGETS, FINDINGS C27, PROMPT note.

## 2026-11-04, run 0428Z (scheduled)
- Part 3 (T5) by part rotation. Auditor role until run 0228Z removed its LOCK (~04:31Z); local Lean available (elan).
- First blind measurement of the current pipeline: red team F (Sonnet) seeded 8 wrong claims against 7221e29; the CI-equivalent judge accepted all 8 (control accepted).
- Four strengthenings (LEDGER): independent second readings (StatementDeps), frozen docstrings of classified definitions, spec fields and Checked module docs (`doc:`/`moduledoc:` entries, 180 new), decimals in code spans checked (`check_numbers.py`), pin claims in TRUSTED_DEFINITIONS.md checked (`check_trusted_defs.py`, new CI step). Re-judged: `runs/2026-11-04T0428Z/t5/RESULTS.md`.
- Records: run README, STATE, LEDGER, BLUEPRINT, TARGETS T5 line, PROMPT note (every reader-facing sentence checked or frozen).

## 2026-11-04, run 0628Z (scheduled)
- Part 1 by part rotation (the "simulations" link had no checker). Local Lean available (elan).
- First rigorous simulator: validated ODE enclosure in Lean (rational Taylor cells, exact defect bounds, energy box, Mathlib Grönwall). Frozen, proved (Work), audited: every solution of the Duffing IVP x'' + x + x³ = 0, x(0) = 1, x'(0) = 0 is positive on [0, 1.192005] and negative at 1.192006 (earliest zero in between; closed form agrees); existence by Picard–Lindelöf for a clamped Hamiltonian field.
- Blind restatement (stronger, one-sided) closed in Lean incl. first-zero corollary; blind spec (no sorry) met by the definition; referee STANDS-WITH-CORRECTIONS (docstrings corrected).
- Records: run README, STATE, TARGETS part 1 status, BLUEPRINT, LEDGER, PROMPT note.
- Promotion to Checked (same run): `Checked/Sim/*`, pin of the new `IsDuffingSolution` by the blind spec, two headlines (one-sided form; LEDGER), NV witness, glossary term, relock. CI: next run.

## 2026-11-04, run 0828Z (scheduled)
- Parts 1 and 5 (rotation: part 5 idle since 0028Z). Local Lean available (elan). Duffing promotion CI green: both Duffing headlines PROVED.
- Generic simulator piece: confinement to the Lipschitz region by the enclosure itself (`Work/Sim/Validated.lean`), so a new polynomial system needs only a Lipschitz lemma and generated certificates; existence for the clamped field by the same enclosure.
- Froze, proved (Work) and audited: full mass-action Michaelis–Menten mechanism (k = 1, [S]₀ = [E]₀ = 1): every solution has [P] < 1/2 on [0, 2.5665] and > 1/2 at 2.5666; a solution exists. Blind restatement equal to the program predicate, both blind claims closed; blind spec met; referee STANDS-WITH-CORRECTIONS (three numerical routes; QSSA off by 7–26%).
- Promotion prepared on branch `wip/mm-checked` (pin, NV witness, glossary); relock via the CI author-files artifact next run.
- Records: run README, STATE, LEDGER, BLUEPRINT, TARGETS parts 1 and 5, PROMPT note.

## 2026-11-04, run 1028Z (scheduled)
- Part 3 by part rotation. Local Lean available (elan). Michaelis–Menten promotion CI green: both headlines PROVED.
- Number rule merged from branch and made blocking (citations exempt, negated literals read with their sign, old derived numbers baselined per number).
- Second blind red team (G, Sonnet, 8 defects, ≥ 3 on the simulations) against ad62b38: 8/8 accepted by the CI-equivalent judge. Five strengthenings (LEDGER): units glued to numbers read, citation registry, every Checked docstring frozen, TRUSTED_DEFINITIONS.md lines disclosed, closed audits stay closed (new CI step in the work job). Same defects after: 1/8 (G02). `runs/2026-11-04T1028Z/t5/RESULTS.md`.
- Records: run README, STATE, LEDGER, BLUEPRINT, TARGETS T5 line, PROMPT note.

## 2026-11-04T1228Z (scheduled run)
- Env: add_repo not exposed; repo pre-cloned (stale local main reset); local Lean via elan ok. CI 41824437583 (7d4553b) green.
- Part 2: B1 fourth order. Froze, proved (generated certificates, 8 Ω-pieces), audited (blind restatement closed in Lean, referee STANDS-WITH-CORRECTIONS, Table 2 second-read blind in v1–v4) and promoted `Checked.Cosmography.B1L19.l19_sq_central`, `l19_sqg_central`, `l19_sq_box`, `l19_sqg_box`: the Lusso et al. 2019 quasar-driven fitted curves are not flat-ΛCDM shaped between 1 + z = 2√2 and 4√2 for any Ω ∈ [0, 1]. Trust map 139/139, NV 88/88.
- FINDINGS candidates C28 (L19 "below 2%" sentence), C29 (this result).
- PROMPT: two working notes (stale pre-cloned main; part 2 asks "is the answer already in print?" before freezing; LEDGER experiment).

## 2026-11-04T1428Z (scheduled run)
- Env: add_repo not exposed; repo pre-cloned (stale local main reset); local Lean via elan ok. CI 41839154897, 41846160247 green.
- Part 3: blind red team H (Sonnet, 8 defects vs d714f04): 8/8 accepted on main; blind red team I against all the new checks (f73ba92): 8/8 accepted. New check_prose rule 6 (parameters; blind to H): 3 of 4 generality defects rejected. After reading H: equation-fixed parameters, sign rule, per-headline citations, module-doc numbers (rule 7), guarded unchecked-prose banner in README/STATE; 1/8 accepted. TRUST_MAP.md and the packet show the parameters each statement fixes (generated). `runs/2026-11-04T1428Z/t5/RESULTS.md`.
- Records: run README, STATE, LEDGER (integrity event), BLUEPRINT, TARGETS T5 line, PROMPT note.

## 2026-11-04T1628Z (scheduled run)
- Env: add_repo not exposed; repo pre-cloned (stale local main reset); local Lean via elan ok. CI of run 1428Z green (41857826238, 41858026983, 41858972093, 41861547449).
- Part 1, data claims (the link had no checker): Farooq & Ratra 2013 Table 1 (28 H(z) points), flat law, H₀ marginalised over the paper's Gaussian priors. Froze, proved (no floating point: closed-form Gaussian integral, AM–GM square-root bounds, generated certificates), audited (blind restatement closed in Lean incl. the H₀ > 0 integration range; blind second reading of the table agrees in Lean; referee STANDS-WITH-CORRECTIONS) and promoted eight headlines: best-fit Ω intervals, existence, minimum values, transition redshifts for both priors. The paper's printed best fits are grid-rounded minimisers; its transition redshifts are those of the grid values; its χ²_min = 18.24 is reproduced by no natural convention (parked: no conclusion changes).
- Records: run README, STATE, LEDGER, BLUEPRINT, TARGETS part 1 status, PROMPT note.

## 2026-11-04T1828Z (scheduled run)
- Env: add_repo not exposed; repo pre-cloned (stale local main reset); local Lean via elan ok. CI of run 1628Z promotion 41883514176 green (FR13 PROVED).
- Part 5 (idle since 0828Z): acentric factor of the original Redlich–Kwong fluid. Froze (46d5200), proved in Work (2278758; θ-uniform generated certificates, existence by IVT), blind restatement closed in Lean (c1d077d), referee STANDS-WITH-CORRECTIONS (value 0.058 in print, 1983), promoted to Checked (`Checked/Chemistry/RK*.lean`).
- Records: run README, STATE, LEDGER, BLUEPRINT, TARGETS part 5 status, PROMPT note.

## 2026-11-04T2028Z (scheduled run)
- Env: repo ok (pre-cloned, stale local main reset); local Lean via elan ok; CI of run 1828Z promotion 41901099462 green on every job (RK acentric factor PROVED).
- Part 2: B1 extended to closed ΛCDM. Frozen (68ec9c1), proved in Work (3b3c3d6), audited (049f2ac): for every Ω_m ∈ [1/10, 1] and Ω_k ∈ [−1/10, 0] the pinned curved d_L ratio between 1 + z = 2√2 and 4√2 is ≥ 27/10, so the Lusso et al. 2019 central fits miss by > 1/4 and > 3/20 mag. First two-parameter certificates (42 boxes). Blind restatement closed in Lean; referee STANDS-WITH-CORRECTIONS (answer in print qualitatively: Khadka & Ratra 2020/2021, Bargiacchi et al. 2022).
- PROMPT working note: integral-binder precedence trap, two-parameter boxes, Mathlib `Real.sin_gt_sub_cube` (x − x³/6, any x > 0).

## 2026-11-04T2228Z (scheduled run)
- Env: repo ok (pre-cloned; add_repo not exposed); local Lean via elan ok. CI: B1 curvature promotion 41920856539 green (PROVED); LOCK run 41925589071 lost its checked job in nanoda (no log; watched).
- Part 3: `CLAIMS.md`, every headline's claim generated from its Lean statement (`scripts/trust/Claims.lean`; phrases of pinned definitions in `scripts/trust/phrases.txt`, linted and change-guarded by `check_claims.py`); blocking in CI. Validation packet shows the generated claims.
- Blind red team J (Sonnet) against the generated claims: 6/7 valid accepted, all misleading through names/choice/constants, none through false generated text; fixes after reading (slot renaming, choice objects, truncating arithmetic, decimal constants, lookalike names): 1 rejected, 2 correct, 2 disclosed, 1 open.

## 2026-11-05T0028Z (scheduled run)
- Env: repo ok (detached HEAD reset to origin/main); local Lean via elan + cache; CI of run 2228Z green at its final commits; freeze CI 41943224752 green.
- Part 5, first mathematics result: Lane–Emden n = 3 constants (ξ₁, ω₃, ρ_c/ρ̄) for every solution, `Work/Math/LaneEmden.lean`, PROVED in Work (local build, standard axioms); singular start `LEStart.lean`, time-dependent tube cell `LECell.lean`, 90 generated cells; blind restatement closed (`LEBlindBridge.lean`); referee STANDS (`runs/2026-11-05T0028Z/referee_le3.md`). Existence and Checked promotion next.
- Process fix: run README stub with the THE RESULT line in the first commit of a run (goal guard had failed on intermediate commits of run 2228Z).


## 2026-11-05T0228Z (scheduled run)
- Env: repo ok (detached HEAD reset to origin/main); local Lean via elan + cache; CI of run 0028Z green on all three commits.
- Part 5: existence of a Lane–Emden n = 3 solution regular at the centre (`Work/Math/LEExists*.lean`: Banach fixed point of the scaled Volterra map near the centre, Picard–Lindelöf with a dissipative clamped energy after, glued), CI 41957394569 green.
- Promotion to `Checked/Math/` (eleven modules, `runs/2026-11-05T0228Z/scripts/promote_le.py`): headlines `Checked.Math.LaneEmden.laneEmden3_constants` and `Checked.Math.LEExists.exists_solution`, NV witness, relock, CLAIMS.md and packet regenerated; audit `Work/Math/LaneEmdenAudit.lean` registered. Local: full Checked build, trust step 153/153, NV 99/99.
- PROMPT working notes: existence at a regular singular point; promotion by script (min_imports trap, module-doc and docstring rules).

## 2026-11-05T0428Z (scheduled run)
- Env: repo ok (detached HEAD reset to origin/main); auditor role 04:28–04:37Z (run 0228Z's LOCK, < 150 min) until 0228Z released it; local Lean via elan + cache. CI of 0228Z's promotion 71a343e 41968192006: every blocking step of the checked job green (build 38 min, nanoda 10.7 min, trust step 3 min), work, packet, goal guard green: Lane–Emden n = 3 PROVED.
- Part 5 audit: `Work/Math/LaneEmdenNearMiss.lean` — the Checked Lane–Emden headline with θ(0) = 1 − 10⁻⁸, or exponent 5, or exponent 1, is false (proved).
- Part 1 (test suites): Moresco et al. 2016 Table 5 tested, `Work/Data/Moresco16.lean` (frozen 13f0ee8, PROVED in Work, blind restatement closed in `Moresco16BlindClosed.lean`, referee STANDS-WITH-CORRECTIONS): printed AICc and BIC inconsistent in every row under Eq. 5.4; printed oΛCDM and linear BICs above the BIC of an explicit fit. Finding candidate C30 (misprint class, no conclusion changes).

## 2026-11-05T0628Z (scheduled run)
- Env: repo ok (detached HEAD reset to origin/main); no LOCK; local Lean via elan + cache. CI of run 0428Z's commits green (41974363342, 41974602988, 41975164683).
- Part 2 (new science): the global minimum of the open-ΛCDM χ² of Moresco et al. 2016 Table 4 (H₀ prior 73 ± 2.4) certified over the whole parameter region — `Work/Data/Moresco16Min.lean` (frozen 1daa626, PROVED in Work 09b58c7, axioms standard): χ² ≥ 14.9665 for every admissible point, a prior-region point below 14.9675, greatest lower bound 14.967 ± 0.0005; the printed oΛCDM AICc 21.41 unattainable under Eq. 5.4 for every N ≤ 31. 905-box cover, certificates by kernel evaluation over ℚ. Blind restatement (Sonnet) closed; referee STANDS-WITH-CORRECTIONS.
- Probe branch `probe/kernel-decide` (nanoda on `decide +kernel`); PROMPT note on kernel-evaluated certificates.

## 2026-11-05T0828Z (scheduled run)
- Env: repo ok (detached HEAD reset to origin/main); local Lean via elan + cache (full Checked build ≈ 50 min). CI of run 0628Z's later commits: in progress at start (STATE).
- Part 3: definition labels machine-checked (red team J follow-up). FORMULA/MATH/WITNESS/PRINTED definitions behind headlines need a blind second formulation/reading proved equal in Lean or a line in the shrink-only `scripts/trust/formula_baseline.txt`; COMPOSITE/CLAIM bodies only listed definitions; SPEC must pin; unknown labels fail. Blind second formulations (Sonnet, sympy) for 21 definitions, 20 agree, `margChiSq` only for σ > 0. CLAIMS.md shows the agreement per formula.

## 2026-11-05T1028Z (scheduled run)
- Env: LOCK of run 0828Z → auditor role until 10:39Z (probe read: `decide +kernel` passes the checked job once relocked). Local Lean via elan + cache.
- Parts 1, 2: Moresco et al. 2016 data claims and the certified χ² minimum promoted to Checked (`Checked/Data/Moresco16*.lean`, 10 headlines; cover by `decide +kernel`); `m16Table` second reading, blind second formulations of `e2OL`, `chiSqOL`, `chiSqLine` (all agree); NV witnesses; relock; CLAIMS.md; packet. Audit `Work/Data/Moresco16PromotionAudit.lean`.
- Claims.lean: PRINTED definitions with an independent second reading say so in CLAIMS.md.
- 13:37Z (after the records, lock held by run 1228Z; this append and the run folder only): promotion CI 42022359372 green on every blocking step (nanoda 19.6 min); the ten Moresco 2016 headlines are PROVED.

## 2026-11-05T1228Z (scheduled run)
- Env: no LOCK; local Lean via elan + cache. CI: 1783fe6 (Moresco promotion) build 78 min, nanoda 19.6 min green; 70d33e3 checked job lost in nanoda (runner loss).
- Part 5: Peng–Robinson with the 1976 κ(ω) at ω = 1 — p_s/P_c = 0.0114, ω = 0.942 at every critical point and every Maxwell state, existence too; frozen, proved in Work, blind restatement closed, referee STANDS-WITH-CORRECTIONS, promoted to Checked (`Checked/Chemistry/PR*.lean`). The RK generator pattern carried over to PR (√2 logarithms) in one run.

## 2026-11-05T1428Z (scheduled run)
- Env: no LOCK; local Lean via elan + cache (full Checked build ≈ 90 min). CI: PR promotion 6a32db1 42039795953 green (PROVED); LOCK commit 01b0c8c checked job lost (runner loss).
- Part 3: blind red team K (Sonnet, six new headlines vs 01b0c8c) — 6/6 accepted by every check; five new blocking rules (module-level disclosure of second formulations/readings and agreements; COMPOSITE and CLAIM constant rules, `scripts/trust/claim_baseline.txt`; junk-value rule; check_prose rule 8 for names and data words) reject all six; adversary on the new rules, cheapest bypasses closed (`runs/2026-11-05T1428Z/t5/`).

## 2026-11-05T1628Z (scheduled run)
- 16:28Z (LOCK held by run 1428Z; this append and the run folder only): promotion 6a32db1 CI 42039795953 green — `pr_omega1_unique`, `pr_omega1_exists` PROVED; records 46a759e green; 1428Z LOCK commit 01b0c8c: checked job lost 1.5 min into the build (third runner loss today, no log).
- 16:58Z: took over run 1428Z's stale LOCK (run 1428Z was alive and pushed its rules append-only; merged by hand). CI repair: checked job frees disk and adds swap (three runner losses today).
- Part 3: its own blind red team K (Sonnet, snapshot cb0223f) — 6/6 accepted on main, 4/6 blind against run 1428Z's new rules; four more rules (printer/meta code in Checked, structures in the label body rules, COMPOSITE aliases, binder decorations in Claims.lean, check_prose rule 9 for named sources) → 0/6. CLAIMS.md and packet regenerated.

## 2026-11-05T1828Z (scheduled run)
- Env: no LOCK; checkout on main; local Lean via elan + cache; CI 52459ff, 2f294cd, 7bcfeb8 green.
- Part 2 (with part 5): **PR with the revised (1978) κ(ω) at ω = 1 has acentric factor 1.000** (p_s/P_c = 0.0100), every critical point and coexistence state, existence — frozen 7bcfeb8, proved by regenerated certificates 529cd99, blind restatement closed, referee STANDS-WITH-CORRECTIONS, promoted to `Checked/Chemistry/PR78Acentric.lean` (CI: next run).
- Candidate C31: Cantera's coded coefficients of the same correlation differ in two digits and give 0.998 (`Work/Chemistry/PRCanteraAcentric.lean`, PROVED in Work); the consensus coefficients are self-consistent to 10⁻⁴ over ω ∈ [0.6, 1.5] (floating point).
- PROMPT working note: sibling claims by parametrised generators.

## 2026-11-05T2028Z (scheduled run)
- Env: no LOCK; checkout reset to origin/main; local Lean via elan + cache (full Checked build ≈ 44 min). CI: run 1828Z's promotion 414e080 42098722467 green on every job — `pr78_omega1_unique`, `pr78_omega1_exists` PROVED.
- Part 1: `claim_baseline.txt` 28 → 0 and `formula_baseline.txt` 11 → 0. Blind Sonnet second readings (typeset only) of every grandfathered CLAIM's inline data (incl. the formulas behind F1, F2, F9) and of `dQFlat`, `jL`; blind second formulations of the seven remaining formulas (the F9 correction of (11.31) re-derived from the field equations) and of `margChiSq` for every σ. All agree (`Checked/Trust/TranscriptionsClaims.lean`, `Formulations{D,E}.lean`). CLAIMS.md marks CLAIMs read twice. 48 closed audit theorems registered in `audits.txt`.
- PROMPT working note: empty a baseline while a build runs.

## 2026-11-05T2228Z (scheduled run)
- Env: no LOCK; checkout reset to origin/main; local Lean via elan + cache (full Checked build ≈ 52 min). CI: dd055a6 42113143146 and 862bb00 42119105514 green.
- Part 3, blind round L (Sonnet red team on a read-only snapshot, aimed at run 2028Z's evidence route): 5 of 6 valid defects accepted by the checks on main. New blocking `scripts/trust/check_provenance.py`, written blind in parallel by a fork: rejects 5/5. Two StatementDeps rules after reading L (agreements of propositions; inline arithmetic in CLAIMs). Main unchanged under the new rules (167/167, NV 108/108).
- PROMPT working note: forged evidence needs provenance checks, not disclosure.

## 2026-11-06T0028Z (scheduled run)
- Env: repo ok; **local Lean refused** (elan installer denied; CI judge only); previous run's CI green (a8c9e61 42133539198, 9fb02b6 42134383430).
- Part 5 with part 2: **Soave–Redlich–Kwong with Soave's κ(ω) at ω = 1 returns acentric factor 0.992** (p_s/P_c = 0.0102) at every critical point and coexistence state, existence too: frozen, proved by modules emitted from the RK route (first CI attempt), blind restatement closed, referee STANDS-WITH-CORRECTIONS, promoted to `Checked/Chemistry/SRKAcentric.lean` (author files from CI).
- Graboski–Daubert refit: 0.994 (frozen; Work proof on `wip/srkgd`), emitted by the new parametric `variant.py`.
- PROMPT working notes: the no-local-Lean route through the cached work job; digit-bounded constant substitution; sibling SRK claims from one config.

## 2026-11-06T0228Z (scheduled run)
- Env: repo ok; **local Lean available again** (elan + Mathlib cache; `lake build Checked` ≈ 37 min); previous run's CI green (8971901 42145695264: SRK promotion PROVED).
- Part 3, blind round M judged: the checks on main accepted 6 of 6 valid defects (invented "printed" formulas as statement literals, shifted PR coefficients in a sibling, forged reading with its brief, narrowed claim template, RK result under the SRK name, paraphrase dropping the ΛCDM hypothesis). Four new blocking scripts written blind to M (`check_literals`, `check_source_names`, `check_templates`, `check_blind_route`): 0 of 6 accepted, 4 of 6 on the merits.
- First literal readings: the PR 1976, PR 1978 and Soave κ(ω) coefficients of the ω = 1 headlines read by a blind reader and matched token by token (`Checked/Trust/SecondReadingKappa.lean`).

## 2026-11-06T0428Z (scheduled run)
- Env: repo ok; local Lean available (elan + Mathlib cache); previous run's CI green (1b584f7 42158536757).
- Part 1: **the certified simulator handles stiff systems.** One-sided (logarithmic-norm) cell step in a weighted norm (`Work/Sim/OneSided.lean`); Robertson's network (0.04, 10⁴, 3·10⁷) certified at t = 40 for every solution, existence too, 49 generated cells (`Work/Sim/Robertson.lean`, PROVED in Work); blind restatement closed, referee STANDS-WITH-CORRECTIONS, blind spec + pin, blind literal reading.
- PROMPT working note: stiff systems by one-sided bounds; centred polynomials for defect bounds.

## 2026-11-06T0628Z (scheduled run)
- Env: repo ok; local Lean available (elan + Mathlib cache; full `lake build Checked` 57 min); previous run's CI green on main (e8ed35e 42169826483); branch wip/rob-checked: Checked build + nanoda green.
- Part 1: **Robertson promoted to Checked** (`rob_state40`, `rob_exists`): pin, blind literal reading registered, source name, NV witness, relock, TRUST_MAP, CLAIMS, packet; local trust step and every script green; CI 42182848426 pending at the records commit.
- check_literals.py value mode (repair): closed reader constants cover statement atoms of the same exact value (the reading `4 / 100` vs the statement's `(1 / 25)`).
- Long horizons: float feasibility (diagonal weights: no contraction; sheared weights: μ ≈ −2/t) and the per-cell-weight step `Work/Sim/RobCellD.lean`.
- PROMPT working notes: literal readings by value; sheared weights for stiff slow manifolds.

## 2026-11-06T0828Z (scheduled run)
- Env: repo ok; local Lean (elan + Mathlib cache); previous run's promotion CI 42182848426 green on every job (Robertson t = 40 PROVED).
- Parts 2 and 1: **Robertson's stiff network certified at t = 10¹¹** (every solution; existence; blind restatement closed; referee STANDS-WITH-CORRECTIONS), PROVED in Work by local build: 77 generated contracting cells with sheared weights. The Bari test-set reference y₃ = 0.9999999791665050 is more than 10⁻¹⁴ below every solution's y₃(10¹¹) (FINDINGS candidate C-ROBER).
- New generic tools: certified Chebyshev bounds (`Work/Sim/ChebBound.lean`, kernel-checked Clenshaw), sheared-weight contracting cell step with corner PSD certificate (`Work/Sim/RobShear.lean`).
- PROMPT working note: long horizons of stiff systems (Chebyshev bounds, slow-manifold collocation, sheared weights).

## 2026-11-06T1028Z (scheduled run; parts 1/2 and 3)
- Env: local Lean via elan + cache; full `lake build Checked` ≈ 57 min. CI: 8a64b6d 42200080559 green on every job.
- Robertson at t = 10¹¹ promoted to Checked (14 modules by script; `rob_state1e11`, `rob_printed_y3_low`, `rob_exists_1e11` registered; NV; new blind literal reading of the Bari end time and printed y₃ via brief → reading → copy; relock, TRUST_MAP, CLAIMS 174, packet). PROVED once its CI is green.
- check_blind_route B3 false positive on the brief's file template repaired (template lines exempt).
- T5 round N: blind Sonnet red team, 4/6 accepted by the round-M checks; six new blocking checks (literal targets with slots and `+eval`, frozen reader modules, brief leaks, source-name variants, generalising words, grading words): 0/6 after, not blind.

## 2026-11-06T1228Z (scheduled run; part 5)
- Env: local Lean via elan + cache. CI: 7cfdee5 trust step red as expected for an intermediate commit; promotion 6f0816d Checked build green, nanoda running at 13:10Z.
- Mathematics: **Gelfand / Frank-Kamenetskii critical parameter of the 3-D ball certified**: for every solution of the isothermal Emden–Chandrasekhar equation on any [0, S], S ≥ 4.1, max s²e^w attained at s₁ ∈ [4.071496844, 4.071496845], value ∈ [3.321992118, 3.321992119]; global maximum by a Lyapunov energy; existence; blind closure; referee STANDS. PROVED in Work (freeze → proof in ≈ 45 min, every generated module compiled first time after a 6-cell test).
- New tools: `Work/Math/GStart.lean` (singular start with e^w), `GCell.lean` (cell step for E' = Eφ), `GFinal.lean` (Lyapunov assembly), `GHelp.lean` (exp Taylor bounds, positivity extension); generator `runs/2026-11-06T1228Z/scripts/gen_g.py`, `emit_g.py`.
- PROMPT working notes: transcendental nonlinearities by an auxiliary variable; web-tool refusals in subagent briefs.
## 2026-11-06T1428Z (scheduled run; parts 5 and 3)
- Env: local Lean via elan + cache; first full Checked build OOM-killed, rerun ≈ 60 min. CI: 6f0816d green on every job (Robertson t = 10¹¹ PROVED).
- Mathematics: **Gelfand critical parameter of the 3-D ball promoted to Checked** (fb999b2): `gelfand_ball_critical`, `exists_solution` registered, NV witnesses, blind literal reading of the radial problem (`Checked/Trust/SecondReadingGelfand.lean`), relock, CLAIMS, packet. PROVED once CI is green.
- Checks: check_literals (a5) domain lengths (adversary-tested); new `check_claim_words.py` (W1 inference, W2 names, W3 two-sided words, W4 persistence, W5 grades) and check_blind_route B5 (no side file next to a brief), wired into lean.yml.
- T5 round O (blind, against the round-N scripts): 6/6 accepted; after the new rules 1/6 (not blind). `runs/2026-11-06T1428Z/t5/RESULTS.md`.
- PROMPT working notes: domain lengths are not data (reader template with placeholders); full build OOM (heavy modules first, poll ≤ 5 min).
## 2026-11-06T1628Z (scheduled run; part 5)
- Env: local Lean via elan + cache. LOCK held by live run 1428Z at start (48.4): worked in `runs/2026-11-06T1628Z/lean/` only until its release, then took the LOCK (16:58Z).
- Mathematics: **Gelfand problem as a PDE with Mathlib's Laplacian, both directions — radial classical solutions in the unit ball of ℝ³ exist for 0 < λ ≤ 3.321992118 and not for λ > 3.321992119: PROVED in Work + AUDITED** (`Work.Math.GelfandPDE.gelfand_pde_radial_bound`, freeze 194b723, proof 1757139; `Work.Math.GelfandPDEExists.gelfand_pde_radial_exists`, freeze 674cdc4, proof 03bbb04; blind restatements closed; referees STAND).
- New tools: radial functions C² at the origin from profile data and Δ at 0 (`Work/Math/RadialC2.lean`); centre bounds of Gelfand solutions (`GProfile.lean`); radial Laplacian in any dimension (`Work/Math/RadialLaplacian.lean`); continuation of the radial Gelfand ODE from any a > 0 (`GContFrom.lean`); `glue_at`, `ode_bound` (`GelfandODEBound.lean`).
- PROMPT working notes: a live LOCK is not idle time; radial PDE ↔ ODE pattern (both directions); instance trap on `E →L[ℝ] E →L[ℝ] ℝ`.
## 2026-11-06T1828Z (scheduled run; parts 2 and 1)
- Env: local Lean via elan + cache. CI: fb999b2 green on every job (Gelfand λ* PROVED); trust step red on main from 04feda9 (a module name cited as a constant in STATE) — repaired 3147cbb, `precheck_citations.py` now catches it.
- **Thomas–Fermi initial slope certified: −1.58807103 ≤ y'(0) ≤ −1.58807102 for every neutral-atom solution, PROVED in Work + AUDITED** (`Work.Math.ThomasFermi.tf_initial_slope`, freeze 67f4410, proof 7c25ba6; blind closure; referee STANDS). Digits in print are floating point.
- New generic method: Kamke barriers for cooperative systems (`Work/Math/TFCell.lean`), reduction t = √x, w = √y (`TFReduce.lean`), 114 generated cells (`runs/2026-11-06T1828Z/scripts/gen_tf.py`, `emit_tf.py`).
- PROMPT working notes: barriers for shooting problems; reading CI logs.
## 2026-11-06T2028Z (scheduled run; parts 2/1, 5 and 3)
- Env: local Lean via elan + cache. CI: 3147cbb work job green (Thomas–Fermi Work proofs in CI); checked job running at 21:20Z.
- **Thomas–Fermi existence PROVED in Work** (`Work.Math.ThomasFermiExists.tf_exists`, freeze a68afbb, proof 9da31b2): a solution meeting every hypothesis of the slope headline exists — the enclosure −1.58807103 ≤ y'(0) ≤ −1.58807102 is unconditional. Shooting with Mathlib's Picard–Lindelöf flow (`Work/Math/TFEx*.lean`).
- Promotion of both to Checked: **promoted to Checked** (run 2026-11-06T2028Z: `Checked/Math/ThomasFermi.lean`, `Checked/Math/ThomasFermiExists.lean` and 17 supporting modules, statements identical to the Work freezes up to the namespace; registered headlines, NV witness from the existence theorem, blind literal readings of the equation, the nucleus condition, the limit at infinity and the regularity at 0; local full `lake build Checked`, relock 178 headlines on pinned definitions, NV 116/116, every trust script green; PROVED once its CI is green — read next run)
- Prior art: `runs/2026-11-06T2028Z/prior_art_tf.md` (Iacono 2008 unreadable; no rigorous enclosure < 10⁻⁶ found).
- Part 3: blind red team P (6 defects, not judged) in `runs/2026-11-06T2028Z/t5/redteamP/`.
- PROMPT working notes: existence for shooting problems; test-compile reader templates.

## 2026-11-06T2228Z (scheduled run; part 3)
- LOCK: 1414e21 said "remove LOCK" but left it tracked; taken as released (records complete). `scripts/goal_guard.py` now fails a commit whose message has the "remove LOCK" idiom while LOCK is in the tree.
- **Closed-vocabulary paraphrases** (`scripts/trust/check_claim_vocab.py`, blocking): headline paraphrases in CLAIMS.md use only the generated claim's words (not the author's names or binders), function words and the disclosed `scripts/trust/prose_vocab.txt`; numbers only the claim's; no junk-value conclusions (√/log = 0, x/0, `deriv` without differentiability). Baseline 1133 existing keys, shrink-only. `scripts/trust/check_status_lines.py`: a STATE.md status claiming PROVED/checked/promoted names a Checked headline or module. W2 of check_claim_words reads namespaces. CLAIMS.md notation states Mathlib's total-function conventions.
- Part 3: blind red team Q (Sonnet, 6 defects against the first version e72d899) in `runs/2026-11-06T2228Z/t5/redteamQ/`; rules tightened after reading it (not blind). Judging of P and Q after the LOCK release: `runs/2026-11-06T2228Z/t5/RESULTS.md`.
- PROMPT working note: allow-lists, not deny-lists, for reader-facing prose.
- Correction (run 2026-11-06T2228Z, after its records): commit f881708 says "no LOCK present at the time of the edit"; that is wrong — run 2026-11-07T0028Z had taken the LOCK (028f3ae) before f881708 was rebased onto it. f881708 changed only this run's own lines in STATE.md (trust-track bullet, daily-review measure, next-step item 1: the judged P/Q results) and its run README; nothing of run 0028Z was touched. Under 48.4 it should have gone to the run folder only; the holder may revert those STATE lines.

## 2026-11-07T0028Z (scheduled run)
- Env: add_repo not exposed; stale local main reset to origin/main; local Lean via elan (full Checked build ≈ 100 min). CI: 1414e21 Lean step green after 2 h 34 min, nanoda running (read next run). Main's trust step red from 5ec9b9a (STATE.md backticked the word deriv): repaired 4a2f9ca, precheck_citations.py now reads Prop-structure fields.
- Part 5: Gelfand PDE pair promoted to Checked (`gelfand_pde_radial_bound`, `gelfand_pde_radial_exists`): blind literal reading (dimension, ball, C²; range end = the reader's own 30-digit λ*), NV witnesses, 11 vocabulary words, relock, CLAIMS/TRUST_MAP/packet regenerated; local checks green; PROVED once CI is green.
- Part 3: check_claim_vocab V7 (quantifier order; after Q d04), blind red team R (6 defects, not judged), then V7 binder scope, V8 (strength words in names), optimality words barred (after reading R, not blind).
- Screen for the next part-2 target (Townes, Hastings–McLeod, Blasius).

## Run 2026-11-07T0228Z (scheduled)
- Auditor role 02:27–02:51Z under run 0028Z's LOCK (scratch in `runs/2026-11-07T0228Z/`); LOCK taken after its release.
- **Townes soliton shooting bracket** (parts 2/5): `Work.Townes.Shooting.townes_under` / `townes_over` (θ(0) = 2.2062008646 undershoots, 2.2062008647 overshoots, by r = 68/5), frozen 0599a4c, proved 2359ee4 with a singular start + 2 × 123 validated cells (`Work/Townes/`); blind restatement closed (`Work.Townes.BlindClosed`), referee STANDS.
- CI saturation measured and diagnosed (STATE next step 1); no CI result of this run read.
- PROMPT working note: shooting at a regular singular point by the LE/Gelfand cell route; CI queue.

## Run 2026-11-07T0428Z (scheduled)
- Part 3, the judge: CI could no longer finish a checked job (336fca2: every step success, cancelled at the 6-hour limit; lean4export 135 M lines in 5 h 06 min, nanoda 16.5 min). Workflow repaired in two commits (509b011, eaa5149; LEDGER): per-branch run coalescing, base-diff checks against the newest fully green ancestor (`scripts/ci_changes.py`, fail-closed), LOCK-only heartbeats skip the Lean jobs, nanoda in four memoised shards that partition the constants of the single export (`scripts/nanoda_shard.sh`, `scripts/nanoda/ShardMain.lean`; local partition test on TFCell). 30 superseded runs cancelled (IDs in the run README). Positive control branch `control/sorry-axiom-2026-11-07` pushed; CI of this run not yet read.
- PROMPT working note: the judge's own wall time (diagnosis route, new CI mechanics, certificate size as export cost).

## Run 2026-11-07T0628Z (scheduled; parts 2/5, and 3)
- **Townes ground state existence proved in Work + AUDITED** (`Work.Townes.Exists.townes_exists`, freeze 78498eb, proof 14f7a24): a positive, decreasing solution of the 2-D radial equation decaying to 0 with θ(0) ∈ (2.2062008646, 2.2062008647). Four forks with exact interface statements (singular start with parameter, clamped flow, limit lemma, blind closure) + assembly: freeze → proof in 62 min. Blind restatement closed; referee STANDS.
- CI change 3 (39.5, LEDGER): coalescing per heavy job, not per run — a nanoda shard of > 2 h no longer holds the work job of later commits.
- PROMPT working notes: parametrised shooting existence by interface forks; stub imported statements instead of building a certificate chain locally; job-level CI groups.

## Run 2026-11-07T0828Z (scheduled; part 1, parts 2/5, part 3)
- **Kernel-evaluated validated cells** (08f4bd4): `Work/Sim/QPoly.lean`, `Work/Townes/TCellQ.lean`, `Work/Townes/TQData{A,B}.lean`; Townes chains re-certified with computed defect polynomials (statements unchanged); old certificate modules archived. Build ≈ 2 min (was ≈ 40), oleans 26 MB (was 1.4 GB), export +40 k lines per chain, nanoda 95 s.
- **check_literals strict wildcard rule** (30daeda, LEDGER): numbers inside a group matched by a reader's binder are no longer counted as read (new headlines; six baselined κ(ω) headlines grandfathered, known gap).
- **Townes trio promotion prepared** on `wip/townes-checked` (21ba411, 2e29c8f): Checked copies, blind literal reading (9b0daf9 → ec5663a → copy), registrations, NV witnesses, promotion audit. Author files, relock and main fast-forward next run.
- PROMPT working notes: certificates by kernel evaluation; a reader's binder wildcard reads nothing.

## Run 2026-11-07T1028Z (scheduled; parts 1 and 3)
- Auditor role under 48.4 until run 0828Z released the LOCK (10:55Z); the work was staged in `runs/2026-11-07T1028Z/lean/` (5cb27d7, c2c0cb5, db0c9e1) and installed after the LOCK was taken.
- **Thomas–Fermi, Lane–Emden and Gelfand chains re-certified by kernel evaluation** (statements unchanged): new `Checked/Math/{TFCellQ,TFQData,LECellQ,LEQData,LELast,GCellQ,GQData}.lean`, rewritten `TFChain`, `LEChain`, `GChain`; 15 generated `ring`-certificate modules moved to `_archive/Checked/Math/`. TF data 15.8 MB olean (old ≈ 1.1 GB), whole TF chain +38.7 k export lines.
- PROMPT working note: porting a `ring`-certified chain to kernel evaluation.

## Run 2026-11-07T1228Z (scheduled; parts 2/5)
- **Blasius boundary layer, wall shear, proved in Work + AUDITED** (`Work/Blasius/`): every solution of f''' + f f''/2 = 0, f(0) = f'(0) = 0, f' → 1 has f''(0) ∈ [0.33205733621519, 0.33205733621520] (`Work.Blasius.blasius_wall_shear`), and a solution exists (`Work.Blasius.blasius_exists`); freeze 4db71de, proofs f892958, 56ce5fc; blind restatement closed, referee STANDS. First fluid-mechanics result; ≈ 5 rigorous digits in print before.
- Validated simulator on a third-order system: 3-D Grönwall cell (`BCell`), kernel-evaluated cells (`BCellQ`), analytic tail and scaling (`BTail`); existence by a clamped global flow (forks).
- T5 round R judge prepared for main (`runs/2026-11-07T1228Z/t5/`), not run.
- PROMPT working note: certified constants of boundary-value problems on [0, ∞) by scaling + validated cells + a monotone tail functional.

## Run 2026-11-07T1428Z (scheduled; part 3, parts 2/5)
- **T5 rounds R and S judged** (`runs/2026-11-07T1428Z/t5/RESULTS.md`): R blind 4/5 valid defects accepted, main 4/5 (V8 dead); S (this run) blind 6/6; after this run's rules R 0/5, S 1/6 (not blind).
- **Prose rules** (`scripts/trust/check_claim_vocab.py`, `check_status_lines.py`): V8 repaired; V9 unpinned names; V10 bound numerals (dimension, derivative count, glued D); V11 paraphrase relations are quotations of the generated claim; V6 on code spans and number words; S2 status-line count/scope/finality words. Baseline +250 keys on older paraphrases (LEDGER).
- **Controls** (`scripts/trust/controls/prose_rule_controls.py`): 15 cases; both scripts run them first, so a dead rule fails CI.
- **Blasius pair promoted to Checked** (e1cf192): `Checked/Blasius/`, `Checked/Trust/SecondReadingBlasius.lean` (blind literal reading: σ computed by the reader), headlines `blasius_wall_shear`, `blasius_exists`, NV witness; relock, TRUST_MAP, CLAIMS, packet.
- PROMPT working notes: judge trees from one build; controls with every rule; the blind reader computes, not transcribes.

## Run 2026-11-07T1628Z (scheduled; part 1)
- **Defect identities by kernel evaluation** in the Duffing, Michaelis–Menten and both Robertson chains (`Checked/Sim/QResid.lean`, `QResidRob.lean`; converter `runs/2026-11-07T1628Z/scripts/conv_ring.py`; 469 identities, statements unchanged): olean MMCerts 236.6 → 87.8 MB, export 8.4 M → 3.9 M lines (with dependencies).
- **Weighted one-sided cells** (`Checked/Sim/OneSided3.lean`, `Checked/Blasius/BCellW.lean`, `BWData.lean`): the Blasius chain re-certified with error growth e^2.94 instead of ≈ 10¹⁷ — 36 cells, 19 digits, 9.8 MB olean instead of 288 cells, 40 digits, 65 MB; same statements; `BQData` archived.
- PROMPT working note: weighted one-sided cells before more digits; any `ring` over generated data → computed residual + `decide +kernel`.

## Run 2026-11-07T1828Z (scheduled; part 3)
- **Blind round T** (Sonnet, brief 722f1c0 committed first, snapshot 4986002): six defects, all valid; **6/6 accepted** by every check of the snapshot (`runs/2026-11-07T1828Z/t5/RESULTS.md`, `judge_T.sh`, `judgeT.out`).
- **Rules from T (not blind):** `check_claim_vocab.py` V12 (formula code spans are quotations), V13 (name words are claim or disclosed words), V14 (the word a numeral counts), D1 (no two headlines with the same generated claim); acronym split in names; `check_audits.py` R1 (closed run records stay closed). Controls 15 → 23 (+ R1's scratch-repository control). Baseline +535 keys on main. After: 2/6.
- PROMPT working note: the blind rate has not moved in eleven rounds — generate reader-facing text instead of filtering it.
