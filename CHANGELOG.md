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

## Run 2026-11-07T2028Z (scheduled; part 2/5)
- CI read: 0b9051c (merge of `wip/qresid`) green on every job (branch run 42401643361, nanoda shards memoised) — Townes trio and Blasius pair PROVED.
- **New question, screen → freeze → both Work proofs → blind closure in ≈ 45 min:** Hiemenz stagnation-point flow (Falkner–Skan β = 1), wall shear f''(0) ∈ (1.2325876568, 1.2325876569): `Work/Hiemenz/` — `hiemenz_under`, `hiemenz_over` (every solution from the two start values under/overshoots by η = 15/2), `hiemenz_exists` (a solution of the boundary-value problem between them). No scaling symmetry: a genuine shooting problem, closed by certified events + a supremum argument. Referee STANDS-WITH-CORRECTIONS (doc: uniqueness range); independent 31-digit value 1.23258765682028102017…; no rigorous enclosure in print (≤ 8 printed digits).
- Tools: weighted one-sided cells with a state-dependent Jacobian entry (four Sylvester corners), per-cell sign conditions carried along a chain, and a clamped-field variant whose cells prove the clamps inactive (so the certified chain applies to the Picard–Lindelöf flow directly).

## 2026-11-07T2228Z (scheduled run)
- Env: repo ok (add_repo not exposed; pre-cloned checkout reset to origin/main a62dd14); local Lean via elan ok; CI: caa6439 and a62dd14 green on every job (Hiemenz Work proofs judged); acdcfe1 red (LEDGER disclosure one commit late, intermediate).
- **Hiemenz trio promoted to Checked** (5556e24): `Checked.Hiemenz.hiemenz_under`, `hiemenz_over`, `hiemenz_exists`; blind literal reading (brief → reading → copy, 1bd103f/90f7727/acdcfe1); NV witnesses from the new `Checked/Hiemenz/HIVP.lean` (clamps inactive along the certified cells); vocabulary, relock, TRUST_MAP, CLAIMS, packet. Local full build and every trust check green. PROVED once CI 42427258702 is green on every job.


## 2026-11-08T0028Z (scheduled run)
- Env: repo ok (add_repo not exposed; pre-cloned shallow checkout, `git checkout -B main origin/main` = 24caf5b); local Lean via elan ok (full Checked build 59 min); CI: 5556e24 (42427258702) green on every job → **Hiemenz trio PROVED**.
- **Part 3: certified numbers bound to their quantity and argument** (12da5ad, ef070d8): StatementDeps writes each certified value's selector and pretty-printed quantity; `check_numbers.py` S1–S4, P1–P2 with 11 controls; generated table of all 26 certified values at the end of FINDINGS.md; `Checked.Records.F8_sizes`, `F11_sizes` state their arguments as `let`s (values unchanged, relocked; LEDGER). Closes round T d01. Adversary (Sonnet): 7/7 past the first version, 5/7 after (role class open).
- PROMPT working note (selectors; `let` arguments keep the literal baseline a subsequence).

## 2026-11-08T0228Z (scheduled run)
- Env: repo ok; local Lean (elan + cache); full `lake build Checked` 60 min. CI: ef070d8 green; heartbeat dce69bf red on one Actions-API 504 → `scripts/ci_changes.py` retries transient failures, then fails closed.
- Parts 1/5: Lane–Emden simulator generic in the index (`Checked/Math/LENStart.lean`, `LENCell.lean`, `LENCellQ.lean`); index 2 frozen (d65a231), proved (166b676), existence + blind closure (b297597), referee STANDS, blind literal reading (924714c → d2d0608), promoted to Checked: `Checked.Math.LaneEmden2.laneEmden2_constants` (PROVED once CI is green). Index 4 needs weighted cells (float study).
- PROMPT working notes: a table row per run by parameterising the simulator; CI reads the Actions API with retries.

## 2026-11-08T0428Z (scheduled run)
- Env: repo ok (add_repo not exposed; pre-cloned checkout reset to origin/main a6d46f5); LOCK held by run 0228Z until 1a99699 → work prepared in the run folder meanwhile; local Lean (elan + cache); full Checked build 55 min. CI: 7887164 work job green (Homann Work proofs, closed audits); 1a99699 work + nanoda green, checked cancelled by coalescing.
- Parts 2/5: **Homann axisymmetric stagnation-point flow** — freeze 7819e6b/cf4d646, Work proofs 7887164 (96 + 96 kernel-evaluated cells; existence by the ported Hiemenz shooting argument), blind restatement closed, referee STANDS (32-digit f''(0) by two methods; no ≥ 10-digit value or uniqueness proof found in print), blind literal reading (488aa29 → 1c1f4b0), promoted to Checked 129f217: `Checked.Homann.homann_under`, `homann_over`, `homann_exists` (PROVED once CI is green).
- Float study for the Falkner–Skan separation value (next step: the Hiemenz event pair does not carry over for β < 0).
- PROMPT working note (a sibling equation by porting the whole stack; integer ends in emitters; check h at both ends before freezing).

## 2026-11-08T0628Z (scheduled run)
- Env: no LOCK (taken 14723d7); local Lean (elan + cache ≈ 3 min; full `lake build Checked` 06:31–07:45Z). CI read: 129f217 (42453268112, Homann promotion) **green on every job** → Homann trio and Lane–Emden index 2 PROVED (Blasius and Townes now green on a main run too).
- Part 3: the role of every certified number (printed formula / derived quantity / difference / free) is computed from its Lean statement and the checked definition labels, written in its FINDINGS tag (R0) and checked against the words before it (R1–R3) and against cosmographic symbols (R4); F1_printedL0, F2_toy, F2_error, F9_values restated through named PRINTED definitions with blind second readings (`Checked/Trust/TranscriptionsRecords.lean`); F9 now certifies (11.21)'s own F(R₀)/(6H₀²): printed 0.0462 vs corrected −0.875 (ΛCDM). check_literals repaired for negative certified values. Run 0028Z's open role defects replayed: 9/9 rejected (not blind). Blind red team U (Sonnet, FINDINGS only): 6/6 valid defects accepted, all in text beside a correctly tagged number (range phrase, prose coefficient, free-value attribution, input symbol, direction word, unit); no rule added after reading it.

## 2026-11-08T0828Z (scheduled run)
- Env: repo ok (add_repo not exposed; `git checkout -B main origin/main` = ca14a91); LOCK of run 0628Z (alive) → auditor role until it was released (6da944f), LOCK taken a101965; local Lean via elan ok (full Checked build 70 min). CI: 129f217 (Homann promotion) green on every job; fdf09cd red only in the work job's elan download (GitHub 504).
- **Parts 2/1: Falkner–Skan rows β = 1/2 and β = 0 promoted to Checked** in one run: `Checked.FalknerSkan.fs_half_exists`, `fs_zero_wall_shear`, from the certified Homann and Blasius theorems by the proved similarity scaling `FSScale.scale`; re-freeze before proof (stated roundings), blind restatement closed, referee STANDS, blind literal reading (brief 1fad98b → reading fdf09cd → copy), NV witness, relock.
- **Audit correction (Homann, run 0428Z):** the Homann constant is the Falkner–Skan β = 1/2 wall shear ×√2, printed to 15 digits; uniqueness for 0 ≤ β ≤ 1 is reported in print (second-hand). STATE and LEDGER corrected; PROMPT working note (map a new equation into its family before calling a constant new).

## 2026-11-08T1028Z (scheduled run)
- Env: repo ok (add_repo not exposed; `git checkout -B main origin/main` = 7e40c13); no LOCK, taken 46a6de2; local Lean via elan after retries (GitHub 504, releases.lean-lang.org 502). CI: the Lean jobs of 82f01ff–46a6de2 red in lean-action's toolchain download (timeout) → third CI repair step (b6c6f95: toolchain pre-installed with retries).
- **Parts 2/5: the monotone solution of the Hiemenz and Homann problems.** Frozen 46a6de2 and 6d095c2, proved fe97390 and 7e861d8, promoted to Checked: every solution with f'' > 0 has its wall shear in the certified window (`hiemenz_monotone_window`, `homann_monotone_window`), one exists (`*_exists_monotone`), two share one wall shear (`*_monotone_same_wall_shear`). Crocco comparison against the certified shooting solutions; no new numerical certificate. Blind restatements (2; four of six blind statements closed), referee STANDS-WITH-CORRECTIONS. Rejected route measured: ball covers of the shooting parameter need ≈ 200–400 chains per side.

## 2026-11-08T1228Z (scheduled run)
- Env: repo ok (add_repo not exposed; stale local main reset to origin/main = c8c8253); LOCK of run 1028Z (alive) → auditor role until it released the LOCK (9b97320); LOCK taken 817c726. Local Lean via elan + Mathlib cache (2-core container; full `lake build Checked` ≈ 90 min).
- **Audit of run 1028Z's referee:** "given f' → 1, f'' > 0 ⟺ f' < 1" has a gap at zeros of f'' with f' ≤ −1; confirmed by an independent referee (no counterexample numerically; unproved; used by no statement).
- **Parts 2/5: Hiemenz and Homann in the class −1 ≤ f' ≤ 1.** Scratch compiled in auditor role (99b2d26), frozen 804a187, proved 9920ce2, promoted to Checked: every solution with −1 ≤ f' ≤ 1 has its wall shear in the window (`hiemenz_bounded_window`, `homann_bounded_window`), any two are equal on [0, ∞) (`*_bounded_equal`), one exists with 0 ≤ f' < 1 (`*_exists_bounded`). Fencing argument + ODE uniqueness against the straight-line solutions f' ≡ ±1 (`BoundedTools`), then the Checked monotone window and Crocco comparison. Blind restatement closed 6/6 (incl. existence with C³), blind literal reading of the bounds (`SecondReadingBound`), referee STANDS-WITH-CORRECTIONS.
- PROMPT working note (a referee's plain-words lemma is a claim too; prefer hypotheses a reader can check; 2-core build time). Next-step scratch: Falkner–Skan β = 1/2 row in the same class by scaling (`runs/2026-11-08T1228Z/lean/FSHalfBounded.lean`).

## 2026-11-08T1428Z (scheduled run)
- Env: repo ok (add_repo not exposed; stale local main reset to origin/main = 1e384a2); LOCK of run 1228Z (alive) → auditor role until it released the LOCK (85d363c); LOCK taken 5e942e0. Local Lean via elan + Mathlib cache; full `lake build Checked` 76 min. CI: 9920ce2 and 9062ed7 green on every job (1028Z's and 1228Z's promotions PROVED).
- **Part 3: certified numbers of FINDINGS.md only in generated blocks** (`check_numbers.py` G1–G6): each block quotes the record's Lean statement from CLAIMS.md and lists the values with tag, role and printed/derived order; author prose carries no certified number. Blind round V: 6/6 accepted, all in number-free commentary (5/6 contradicted by the adjacent block).
- **Blind round W, the generated layer only:** 1/4 valid defects accepted blind, 2/4 once formalities are repaired; three holes closed structurally (junk values through factors of denominators in pinned definitions; no shared phrases; roles through COMPOSITE bodies). Weakest step named: phrase fidelity.

## 2026-11-08T1628Z (scheduled run)
- Env: repo ok (add_repo not exposed; `git checkout -B main origin/main` = de88fae); LOCK of run 1428Z (alive) → auditor role until it released the LOCK (334af75), LOCK taken 16:52Z; local Lean via elan + cache (full `lake build Checked` 77 min, started at once). CI: 9062ed7 (42491111671) green on every job → bounded-class six and Falkner–Skan rows PROVED.
- **Parts 2/5: Falkner–Skan β = 1/2 in the class −1 ≤ f' ≤ 1** — candidate frozen, blind restatement and referee (STANDS-WITH-CORRECTIONS, prose) in auditor role; frozen 868336e, proved c6a98c8, promoted e62e945: `fs_half_bounded_window`, `fs_half_bounded_equal`, `fs_half_exists_bounded` by scaling the Checked Homann theorems; no new certificate, no new numeral.

## 2026-11-08T1828Z (scheduled run)
- Env: repo ok (add_repo not exposed; `git checkout -B main origin/main` = bba2fff); no LOCK, taken d259163; local Lean via elan + cache (full `lake build Checked` 72 min). CI: 868336e, c6a98c8 green on every job; e62e945's checked job cancelled by coalescing (β = 1/2 bounded-class trio not yet PROVED).
- **Part 3: phrase fidelity.** Pinned definitions' bodies printed from Lean next to their phrases; phrases formula-free (P1), first glossary term their own (U2), every word quoted from the blind spec (P2, shrink-only baseline); substituted slots bound to the body's symbols. Blind red team X (before the rules): 6/6 accepted → 0/6 after the rules a fork wrote blind; blind red team Y (against P1/U2): 6/6 past → 1/6 after P2 (not blind). Open: role and sign words of phrases.

## 2026-11-08T2028Z (scheduled run)
- Env: repo ok (pre-cloned, shallow, stale local main reset to origin); local Lean via elan ok (after the CI repair below); CI 42511639502 (e172f1e) green on every job → Falkner–Skan β = 1/2 bounded-class trio PROVED.
- CI repair: a `.lake` symlink committed by run 1828Z moved to `_archive/`; `.gitignore` gains `.lake`; new goal-guard step rejects tracked symlinks outside `_archive/`.
- **Falkner–Skan β = 1/5 row** (class −1 ≤ f' ≤ 1: window (0.6867081809, 0.6867081811), equality, existence) frozen, proved, blind-closed, blind-read, referee STANDS, promoted to Checked (26d2718); PROVED once CI is green.
- **Falkner–Skan β = 1/10 row** frozen (1ebeba5), referee STANDS, blind restatement and blind reading committed; Work proofs generated by the new row driver `runs/2026-11-08T2028Z/scripts/make_row.py`.
- PROMPT working notes: a table row is one command; never commit a worktree's `.lake` symlink.

## 2026-11-08T2228Z (scheduled run)
- Env: repo ok (add_repo not exposed; `git checkout -B main origin/main` = 5481cb7); LOCK of run 2028Z (alive) → auditor role until it released the LOCK (816c21b); LOCK taken 476bf0a; local Lean via elan + cache (full `lake build Checked` 77 min). CI: promotion 26d2718's checked job cancelled by coalescing (read later runs).
- **Part 3: phrase roles, signs and names bound to blind readings.** Blind role reader (95 roles, 13 sign conventions) and blind name reader (23 names with qualifiers), copied verbatim to `scripts/trust/phrase_roles.txt`; `check_claims.py` P3–P6 and the brief → reading → copy route check; all 23 phrases reworded; CLAIMS/FINDINGS/packet regenerated. Blind red team Z: 6/6 accepted by the old rules, same moves 5/6 rejected now (2 by the blind-designed P3). Open: relation sentences outside blind sign clauses.
- Scratch (parts 2/5): f' ≤ 1 is automatic for the stagnation-point equations; Hiemenz/Homann windows restated with only −1 ≤ f' (`runs/2026-11-08T2228Z/lean/UpperBound.lean`, compiled).
- PROMPT working note (roles, signs and names of phrases come from blind readers).

## 2026-11-09T0028Z (scheduled run)
- Env: repo ok (add_repo not exposed; `git checkout -B main origin/main` = fb863a8); no LOCK, taken 6e00d7a; local Lean via elan + cache (full `lake build Checked` 73 min). CI: ae8e18b (42535496360) green on every job → β = 1/5 trio PROVED.
- **Parts 2/5: the class −1 ≤ f' ≤ 1 removed.** Research subagent's proof (`runs/2026-11-09T0028Z/coppel/REPORT.md`) for K = 1/β ≥ 1: every solution with f(0) = f'(0) = 0, f' → 1 has f'' > 0. Lean core (`Work/FalknerSkan/UnrestrictedCore.lean`), freeze d71bf54, blind restatement + referee 84609a7 (STANDS-WITH-CORRECTIONS), proofs 5ae2ab6, blind closure, promotion 3684e58 (`Checked/FalknerSkan/LimitCore.lean`, `Limit.lean`; eight `*_limit_*` headlines; 218 headlines, NV 145/145).
- Checks worked as designed: check_claim_vocab V13 rejected the name "Unrestricted" (generality word in a headline name); check_literals kept the general-β theorem out of the headline set until its literals are read blind.
- PROMPT working note (a research subagent for the missing lemma; name modules after the hypotheses they keep).

## 2026-11-09T0228Z (scheduled run)
- Env: repo ok (add_repo not exposed; `git checkout -B main origin/main` = 4a00073); no LOCK, taken 1201ad2; local Lean via elan + cache (full `lake build Checked` 73 min). CI: 3684e58 (42549988367) work job green, checked job cancelled by coalescing → the eight `*_limit_*` headlines wait for the next green main run.
- **Part 3: phrases of pinned definitions generated from blind texts.** Clause reader (104 lines) and letter reader (q, j, s, l) under brief → reading → copy; `check_claims.py` P7 (coverage by blind texts, neutral connectives, marks as tokens, verb touching the NAME), P8 (registry cannot lose a line), P9 (every registry clause shown; shrink-only `phrase_clause_baseline.txt`, 30 exclusions with reasons); 23 phrases generated (`runs/2026-11-09T0228Z/scripts/gen_phrases.py`); CLAIMS.md, FINDINGS blocks, packet regenerated; 7 neutral nouns disclosed in `prose_vocab.txt`.
- Measured: blind red team AA (P7 stated before it ran) 6/6 accepted by the old rules, same moves 6/6 rejected by P7; adversary AB on P7 as first written 4/5 accepted, 0/5 after the repair (not blind); round Z d01 closed (`runs/2026-11-09T0228Z/t5/judge_AA.out`).
- PROMPT working note: a phrase is generated from blind texts, not written; neutral glue only.

## 2026-11-09T0428Z (scheduled run)
- Env: repo ok (add_repo not exposed; `git checkout -B main origin/main` = 0c7da92); no LOCK, taken 64f429d; local Lean via elan + cache (full `lake build Checked` 86 min). CI: 0c7da92 (42560201836) green; promotion ed98bf4/1df8963 (42571761542): next run.
- **Parts 2/5:** Falkner–Skan β = 1/10 promoted to Checked (window, equality, existence in the class −1 ≤ f' ≤ 1) with its no-bound pair (`LimitTenth.lean`), and `fs_monotone_of_limit` (0 < β ≤ 1: every solution has f'' > 0) registered after a blind reading of its β-form equation (brief e44788a → reading b7ad60e). Headlines 218 → 224, NV 145 → 150; blind restatement of the pair closed (`FTLBlindClosed.lean`).
- Research subagent (Opus) on β < 0: both branches at β = −0.1, −0.15; uniqueness in 0 ≤ f' ≤ 1 fails at β = −0.1 (continuum with algebraic decay, re-checked in the main session by scipy); tail-condition uniqueness proof and shooting events proposed (not frozen; STATE next step 2).
- LEDGER: promotion line, prose_vocab `tenth`/`pressure`/`gradient`, second-reading disclosure. PROMPT working note: a mid-build import of a new module costs one incremental pass (planned).

## 2026-11-09T0628Z (scheduled run)
- Env: repo ok (add_repo not exposed; `git reset --hard origin/main` = ab22cd6); no LOCK, taken eefdb24; local Lean via elan + cache (full `lake build Checked` 87 min). CI: promotion 1df8963 (42571761542) green on every check step read (author-files step still running).
- **Part 1 (rotation, ten runs idle): hypothesis necessity (T2b).** `necessity%` / `dropped%` in `Checked/Trust/NonVacuity.lean`; StatementDeps classifies all 794 hypotheses of the 146 conditional headlines (TRUST_MAP.md, report-only); `Checked/Trust/Necessity.lean` (165 generated witnesses). Measured: 155 needed, 17 redundant, 622 open.
- Adversary (Sonnet) on the first version: no false NEEDED; caveats (total arithmetic, one hypothesis at a time) stated; numbering aligned with CLAIMS.md before the first commit.
- PROMPT working note (classify every hypothesis; cheap counterexamples for boundary-value headlines); TARGETS T2 status.
## 2026-11-09T0828Z (scheduled run)
- Env: repo ok (add_repo not exposed; `git checkout -B main origin/main` = f8fcf46); LOCK of run 0628Z alive → auditor role, released at 933f48e, taken 3396ae3; local Lean via elan + cache. CI: f8fcf46 (42580931850) green; 881ec81, 21de9a4, 0e999ee: next run.
- **Parts 2/5, β < 0 (new ground):** referee (no lemma wrong, six gaps) + prior-art screen of the run-0428Z research note; four theorems PROVED in Work + AUDITED: `fs_neg_decay_max_shear`, `fs_neg_decay_equal` (every β < 0, class f'' > 0 + faster-than-every-exponential approach), `fs_neg_tenth_exists_decay`, `fs_neg_tenth_not_unique` (β = −1/10: two solutions with 0 ≤ f' ≤ 1, f'' > 0, f' → 1 and different wall shear). Certified chains for the adverse-sign K = 10 field (`Work/FSNeg/`), blind restatements closed (`NDBlindClosed`, `NTBlindClosed`). Promotion to Checked next (STATE next step 2).
- PROMPT working note: interface-first forks and auditor-role preparation.

## 2026-11-09T1028Z (scheduled run)
- Env: repo ok (add_repo not exposed; `git checkout -B main origin/main` = 92c7b40); no LOCK, taken fa2194d; local Lean via elan + cache (full `lake build Checked` 95 min). CI: 92c7b40 (42593702186) work job green; checked job and this run's pushes: next run.
- **Parts 2/5:** Falkner–Skan β < 0 promoted to Checked: `fs_neg_decay_max_shear`, `fs_neg_decay_equal`, `fs_neg_tenth_exists_decay`, and the new literal-free `fs_neg_tenth_outside_decay` (frozen d6dc129; replaces the author constant 3 of the Work helper by the decay condition itself; blind restatement closed in `NOBlindClosed.lean`). Headlines 224 → 228, NV 150 → 152, needed hypotheses 155 → 158 (decay hypotheses of both uniqueness theorems).
- Blind literal readings: `fsnWedgeRhs`, `fsnDefectBelow` (600017e → 0c8270b), `fsnWallValue` (eef88ef → 8eb3ece). Prior-art screen: substance classical (Iglisch & Kemnitz 1955, Hartman 1964); no machine-checked version found.
- LEDGER: promotion, reader disclosures, prose_vocab `neg`/`decay`/`max`/`outside`. Lessons in the run README (author constants in ∃-conclusions; wall values need a reading).
## 2026-11-09T1228Z (scheduled run)
- Env: repo ok (add_repo not exposed; `git checkout -B main origin/main` = 8eb3ece, unshallowed); LOCK of run 1028Z alive → auditor role 12:27–13:38Z, released at 8cd5eb6, taken 5c5c02f; local Lean via elan + cache. CI: 83ebad4 (42626827566) in progress; 9149f56, 9f7db47: next run.
- **Parts 2/5, β = −1/10:** four theorems PROVED in Work + AUDITED (frozen 9149f56, proved 9f7db47): `fs_neg_tenth_reversed` (reversed-flow solution in the decay class, −0.1405462131 < f''(0) < −0.1405462129), `fs_neg_tenth_two_decay`, `fs_neg_tenth_window` (0.3192697598 < f''(0) < 0.3192697599), `fs_neg_tenth_monotone_lt`. Certified tube over the whole window replaces Lemma D. Blind restatements 2/2 closed; referee 0 defects in statements; screens: printed −0.140546 agrees, no attached value printed at β = −0.1.
- PROMPT working note (a tube over the parameter window; events must be strict at their time).
## 2026-11-09T1428Z (scheduled run)
- Env: repo ok (add_repo not exposed; `git checkout -B main origin/main` = 9e1586d); no LOCK, taken bcdb283; local Lean via elan + cache (full `lake build Checked` in the background). CI: 83ebad4 (42626827566) checked job cancelled by coalescing; 3dcc21f (42635575605) checked job: see the run README.
- **Part 3 (rotation):** phrases of pinned definitions are now produced by CI from blind readings: P10 (subject, verb, article of every property from a blind shape reader; the second reading, given the blind NAMEs, matched the former PRED exactly, so no phrase changed) and P11 (phrases.txt must equal the fixed template's output; `check_claims.py --generate`), both stated before blind red team AC; P11a–c and P12 after AC and adversary AD (invisible characters, reader order, one block per reader file, join anchors, excluded lines never re-enter). Blind AC 6/6 accepted before, 0/6 after (blind 3/6); AD 4/4 → 2/4 (open: new readings restating excluded overclaims).
- Planted controls of the P3 route and P12 (`scripts/trust/route_control.py`, CI goal-guard job); check_literals rule-1 hint for author constants in conclusions.
- PROMPT working notes: regenerate phrases with `--generate`; brief a reader with the neighbouring blind texts; suspect a control that passes a bad case.
## 2026-11-09T1628Z (scheduled run)
- Env: repo ok (add_repo not exposed; unshallowed, main reset to origin/main = 8c80eb9); no LOCK, taken f86992b; **local Lean refused** (elan installer denied) → promotion through CI on branch `wip/fsneg-tenth-promo` (42655917163, 42656137172: Checked build green twice), Python checks local on the author files.
- **Parts 2/5: Falkner–Skan β = −1/10 reversed-flow solution, decay-class pair and ten-decimal attached wall shear promoted to Checked** (12 modules, 4 headlines 228 → 232, NV 154/154, necessity: f'' > 0 of the β < 0 uniqueness/largest-shear theorems NEEDED, 158 → 161). Merge c143ec5; PROVED once its main run is green on every job.
- prose_vocab `reversed`, `lt` (V13); Work `NAssemble` module doc fixed (scaling, sign); CI author-files tarball carries `.lake/phrases.jsonl` (39.5).
- PROMPT working notes: unshallow at start; a promotion without local Lean in two CI rounds (everything in the first push; STATE citations and module-name words checkable before it).
## 2026-11-09T1828Z (scheduled run)
- Env: repo ok (add_repo not exposed; main reset to origin/main = 739510a); no LOCK, taken 254d087; **local Lean available** (elan installer accepted; full build in the background); CI: c143ec5, 739510a checked job cancelled by coalescing, 254d087 run had no job (GitHub side) → the β = −1/10 promotion still awaits a checked job on main.
- **Part 3: rule P13, phrase lines certified in Lean** (`Checked/Trust/PhraseCerts.lean`, `scripts/trust/phrase_certs.txt`, shrink-only `phrase_cert_baseline.txt`, `check_claims.py` P13 + planted controls, `Claims.lean` prints certificate conditions after phrases and writes `PHRASE_LINES.md`, CI staleness check): 31 of 92 reader lines proved; five shown lines false at edge values now carry their conditions (Ω0 > 1, redshift 0 at coinciding times, orders 0 and 1 cosmographic coefficients, curvK sign, Duffing initial velocity).
- Adversary AE (Sonnet) on the first version: 6/6 defect classes passed; repaired before the first push, 2 open (`runs/2026-11-09T1828Z/adversary/JUDGE.md`).
- PROMPT working note: certify what a reader line says, not who wrote it.
## 2026-11-11T0028Z (scheduled run)
- Env: repo ok (add_repo not exposed; main reset to origin/main = 115b29e); LOCK of run 2026-11-09T2228Z ≈ 25 h old, taken over (626006c); no run on 2026-11-10 (usage limit); **local Lean available** (full build ≈ 78 min). CI 42721774680 (115b29e) green on every job → β = −1/10 Falkner–Skan PROVED, P13 live.
- **Part 1 (T2b): `Checked/Trust/NecessityB.lean`** — run 2228Z's scratch batch completed plus four families (junk critical points of the cubic isotherm, de Sitter vs coefficient laws, lookback with 1 + t², `ne_a0_of_hubble` ×24, `not_littleO_core` ×7): NEEDED 161 → 253, REDUNDANT 17 → 51, fully classified headlines 0 → 22 of 150.
- **New blocking check `scripts/trust/check_necessity.py`** (N1–N3, baseline `necessity_open_baseline.txt`, planted controls); adversary on the first draft found 7 holes, repaired before going live.
- PROMPT working notes: necessity witnesses by family + the ratchet; runs end without warning (push scratch at once).
## 2026-11-11T0232Z (scheduled run)
- Env: repo ok (add_repo not exposed; main = origin/main 3e54961); no LOCK, taken 51906d8; **local Lean available**; CI 42944553092 (3e54961) green on every job (NecessityB + `check_necessity.py` live).
- **Parts 2/5: the Falkner–Skan separation value** — `fs_separation_exists` (β ∈ (−0.1988377351, −0.1988377350) with a zero-wall-shear profile in the decay class) and `fs_separation_unique` (at most one such β), PROVED in Work + AUDITED (blind restatements closed, referee STANDS; independent β* to ≈ 35 digits). First shooting in a coefficient of the equation (`Work/FSSep/`). Prior art: no rigorous enclosure found; two printed values wrong in the 7th–8th digit (candidate C-FS-SEP).
- **Promoted to Checked the same run** (branch `wip/sep-promo`, fast-forwarded): headlines `fs_separation_exists`, `fs_separation_equal` (234 headlines, NV 155/155), blind literal reading (third brief; the first leaked a denominator, the second was committed with a rename), two necessity witnesses (decay conditions needed); every local check green.
- PROMPT working notes: shooting in an equation parameter; reader briefs committed alone with no numeral of the answer.
## 2026-11-11T0428Z (scheduled run)
- Env: repo ok (add_repo not exposed; detached checkout, `git fetch --unshallow`); LOCK held by run 0232Z at start → auditor role (writes only in `runs/2026-11-11T0428Z/`) until 0232Z released it (05:39Z), LOCK taken 0b5193d; **local Lean available** (full `lake build Checked` 60 min).
- **Part 3 (rotation: no part-3 progress for four runs): blind red team AF against hypothesis necessity (T2b)** — 5/6 accepted as submitted (6/6 with a trivial repair): assumptions outside the necessity numbering or classified only formally, each inflating the "every hypothesis classified" tally. Fix (not blind): generated `shape:` entries (StatementDeps `necShape`) + blocking N4 with a shrink-only baseline → 0/6 after. The honest fully-classified count falls 22 → 14 (26 model predicates are bundles).
- PROMPT working note: completeness tallies must be computed on what the reader reads.
## 2026-11-11T0628Z (scheduled run)
- Env: repo ok (add_repo not exposed; detached checkout, `git fetch --unshallow`, main = origin/main 0b5193d); LOCK held by run 0428Z (alive) → auditor role until it released the LOCK at 06:31Z, taken 8ce63fc; **local Lean available** (elan; full `lake build Checked` 06:32–08:07Z). CI: no main run green since 3e54961 (every later run cancelled while pending by the next push); 42984797370 (96a1175) running at the end.
- **Part 1 (T2b): `Checked/Trust/NecessityD.lean`, 70 hypotheses classified** — NEEDED 255 → 303, REDUNDANT 51 → 73, open 555 → 485, fully classified headlines 14 → 29 of 151. Families: printed-coefficient conditions of the cosmographic `_fails` headlines (17, printed = correct models), `H₀ ≠ 0` (4 needed by a static model, 12 redundant by `x/0 = 0`), smoothness of every correct-order distance and lookback series (one derivative too few, `compare_general`), smoothness under the ΛCDM/CPL laws (7 redundant, bootstrap), f(R) slow-roll ranges, printed l₀/m₀ conditions, the critical cubic and all of `exists_unique_critical`, four hypotheses of the separation pair (toy profile).
- Integrity event: one force-push on this run's own wip branch (LEDGER); old head preserved.
- PROMPT working note: necessity by one derivative too few, and by comparison.
## 2026-11-11T0828Z (scheduled run)
- Env: repo ok (add_repo not exposed; detached checkout, unshallowed); LOCK of run 0628Z at start → auditor role until its release (7f5e9c6), LOCK taken 062b036; **local Lean refused** (elan installer denied) → CI only; CI very slow (seven Lean runs at once, > 90 min builds); three superseded branch runs cancelled by hand.
- **Parts 2/5: C-FS-SEP typeset-read** (Fazio 2012 Fig. 4, 2020 Fig. 7: β_min = −0.1988376), blind literal reading `fsSepPrintedFazio`, and the refutation `fs_separation_below_printed` (β < −0.1988376; corollary of the separation window) with NV witness, necessity h1–h3, blind restatement closed in Lean — on `wip/sep-printed-promo` (efdb2d6): built, nanoda-checked, every Python check green on CI author files but one docstring relock; merge handed to the next LOCK holder.
- **New target frozen:** `Work/FalknerSkan/Neg1988.lean` — the attached wall shear at β = −0.1988 in (0.0052181, 0.0052182); five printed values (Fazio, Asaithambi, Zhang, Salama, Zhu: 0.005221–0.005229) are wrong in the 4th digit (candidate C-FS-1988, two independent numerical routes).
- PROMPT working note: referee side observations are FINDINGS candidates the same run.
## 2026-11-11T1228Z (scheduled run)
- Env: repo ok (add_repo not exposed; detached checkout, unshallowed); LOCK held by run 0828Z, then by run 1028Z (13:04Z) → auditor role the whole run (writes only in `runs/2026-11-11T1228Z/` + this entry); **local Lean available** (elan).
- **Parts 2/5: the reversed-flow Falkner–Skan branch at β = −0.1988, PROVED locally + AUDITED** (frozen c9be92b before any proof): a decay-class solution with f''(0) ∈ (−0.00515743, −0.00515741); two decay-class solutions; **Fazio's printed reversed value −0.005158 refuted** (its IVP overshoots f' = 1 — no solution with f' ≤ 1 has it). New generic stack `Work.FSRev.*` (reversed branch for every K ≥ 5) and `RIdent.ident` (unclamped solution = clamped flow while strictly inside the clamps: one ball chain refutes a printed shooting value). Blind restatement closed (all three); referee STANDS-WITH-CORRECTIONS, independent −0.005157420177929. Sources in the run folder; hand-off (move to Work after run 1028Z's promotion, FINDINGS C-FS-1988R draft) in its README.

## 2026-11-11T1028Z (scheduled run; auditor role 10:28–13:04Z, then LOCK)
- **Parts 2/5: the attached Falkner–Skan wall shear at β = −0.1988 certified and promoted** — `Checked.FalknerSkan.NegWallShear.fs_neg_wall_shear_window` (every decay-class solution: 0.0052181 < f''(0) < 0.0052182) and `fs_neg_wall_shear_exists_decay`; five printed values (0.005221–0.005229) outside the window, one (Guo et al. 2020, 0.005218, typeset-read) its correct rounding (candidate C-FS-1988). Blind restatement closed in Lean, referee STANDS-WITH-CORRECTIONS, blind β reading from the typeset page.
- **New stack `Checked/FSAtt/`**: the β = −1/10 attached-flow route generic in the scaled coefficient K ≥ 5 (every β ∈ [−1/5, 0)); new rows are generator runs. Emitter `runs/2026-11-11T1028Z/scripts/emit_att_wc.py`, promotion script `promote_n1988.py`.
- Run 0828Z's printed-value promotion (`fs_separation_below_printed`, efdb2d6) merged in the same local build, relock, Claims and Python trust suite.
- `scripts/trust/precheck_citations.py`: «»-quoted structure fields (the Lean check resolved a backticked `open` in STATE to one; main's trust step was red from fe01874).

## 2026-11-11T1428Z (scheduled run)
- Env: repo ok (add_repo not exposed; detached checkout); no LOCK; **local Lean available** (elan; full build from scratch ≈ 100 min).
- **CI read and repair:** run 1028Z's push a00b1b4 (run 43031110000) was green except the checked job's frozen step: `check_necessity.py` N2 wanted the new headline disclosed by its TRUST_MAP name. LEDGER line added. New `scripts/trust/local_frozen_step.py [--trust] <base>` runs both CI trust steps, read from lean.yml, locally.
- **Part 1, T2b item 3e (red team AF): per-conjunct necessity.** `necessity% thm i j` / `dropped% thm i j` (NonVacuity); StatementDeps closes `bundled i` when every conjunct is classified and none hides a conjunction under a binder; check_necessity parses the new parts fail-closed (10 new planted controls). `Checked/Trust/NecessityF.lean`: 22 witnesses. Fully classified headlines 29 → 32 of 153 (vdW, RK, PR critical constants). First version closed 11 (40/153); run 1628Z's review (binder-nested conjuncts) corrected it before any green main.
## 2026-11-11T1628Z (scheduled run; auditor role 16:28–17:14Z, then LOCK)
- Env: repo ok (add_repo not exposed; detached checkout, unshallowed); LOCK of run 1428Z (alive) → auditor role until its release (dc2f575), LOCK taken 89d717f; **local Lean available** (elan; full `lake build Checked` 85 min).
- **Part 1, T2b item 3e: parts replace conjuncts** — `necessity%/dropped% thm i j` now drop one *part* (through ∧, ∃, ∃!, ∀, ∀ᶠ, ↔, an implication's conclusion) by replacing it with `True`; `Checked/Trust/NecessityF.lean` in parts semantics with 14 new redundancy witnesses: the seven flat ΛCDM/CPL headlines are fully classified. Fully classified 32 → 38 of 153.
- **Part 3: blind red team AG** (Sonnet, brief committed before the round) got 6/6 wrapper headlines reported "fully classified" with hidden bundles (∃/∀→/∃! heads, `NNReal`, restatement through `Set.Ioi`, fuel exhaustion). Repaired in `StatementDeps.lean` `necShape` + `partsWalk` → 0/6 after (not blind; judged with a build). N4 now lets existing headlines gain shape reasons: 11 newly flagged.
- PROMPT working note: a shape detector must use the same walk as the obligations it gates.
## 2026-11-11T1828Z (scheduled run; auditor role 18:28–18:44Z, then LOCK)
- Env: repo ok (add_repo not exposed; detached checkout, unshallowed); LOCK of run 1628Z (alive) → auditor role until its release (b7afee7), LOCK taken 537b5e2; **local Lean available** (elan; full `lake build Checked` 88 min).
- **Parts 2/5: the reverse-flow Falkner–Skan trio at β = −0.1988 promoted** (`Checked/FalknerSkan/NegReversedWallShear.lean`, stack `Checked/FSRev/`; run 1228Z's scratch merged into Work first). The blocking gap — no non-vacuity witness for "every solution of the printed-value IVP overshoots" — closed by a global-existence proof (`RGlobal`: dissipative clamped tail with a nonincreasing energy; `RPrintedNV.printed_ivp_exists`). Printed value −0.005158 typeset-read and read blind (`fsRevPrintedWallFazio`); necessity 2, 3, 6 witnessed (`NecessityG`). Candidate C-FS-1988R.
- PROMPT working note: non-vacuity of an initial-value statement by a clamp under which the energy decreases.

## 2026-11-11T2028Z (scheduled run; auditor role 20:28–21:24Z, then LOCK)
- Env: repo ok (add_repo not exposed; detached checkout, unshallowed); LOCK of run 1828Z (alive) → auditor role until its release (df9f9eb), LOCK taken dcd724a; **local Lean available** (elan; full `lake build Checked` ≈ 60 min after the Mathlib cache).
- **Part 1, T2b:** −1 ≤ f' ≤ 1 with f(0) = f'(0) = 0 forces f' → 1 for every positive product coefficient (`Checked/FalknerSkan/BoundedLimit.lean`, new elementary proof, ≈ 250 lines); 45 witnesses in `Checked/Trust/NecessityH.lean`: the far-field condition and each part of the velocity bound of the ten bounded-class Hiemenz/Homann/Falkner–Skan headlines are REDUNDANT. REDUNDANT 73 → 88, open 502 → 487, shape baseline 27 → 17.
- PROMPT working note: ask whether the other hypotheses imply a condition before hunting a counterexample; `dropped%` binder order of equality headlines; module-name clashes between overlapping runs.

## 2026-11-11T2228Z (scheduled run; auditor role 22:27–22:53Z, then LOCK)
- Env: repo ok (add_repo not exposed; detached checkout with an unrelated stale local `main`, reset to origin/main); LOCK of run 2028Z (alive) → auditor role until its release (53d4d4c), LOCK taken 647b974; **local Lean available** (elan; Mathlib cache ≈ 3 min). A full `lake build Checked` was OOM-killed once (B1L19 curved certificates next to TFQData; rebuilt with the certificate modules first, serially).
- **Part 1, T2b: f(0) = 0 NEEDED in 24 boundary-value headlines, 34 hypotheses** (suction witnesses): Blasius and β = 0 by an elementary global-existence argument (no shooting: scaling symmetry); Hiemenz, Homann, β = 1/2, 1/5, 1/10 by the existing shooting stacks ported to a free wall value of f by script, with new kernel-evaluated cells; every generated module compiled first time. The ten bounded-class headlines and the Blasius / β = 0 wall-shear headlines are now fully classified.
- PROMPT working note: parametrise the start of a shooting stack to witness initial/wall conditions.

## 2026-11-12T0227Z (scheduled run)
- CI 43128169409 (1727c31) red only at `check_status_lines` S2 (one STATE word); repaired 31bb06c; `precheck_citations.py` now also runs `check_status_lines.py`.
- Part 1: `Checked/Trust/NecessityL.lean` — 100 hypotheses classified (B1 family: 80; pinning theorems: 20). NEEDED 343 → 414, REDUNDANT 88 → 117, open 453 → 353, fully classified 50 → 54 of 154.
- PROMPT working notes: `[skip ci]` on scratch/heartbeat pushes; necessity witnesses for model-based families.

## 2026-11-12T0427Z (scheduled run; auditor role 04:27–04:58Z, then LOCK)
- Env: repo ok (add_repo not exposed; detached checkout, unshallowed); LOCK of run 0227Z (alive) → auditor role until its release (89aca37), LOCK taken b74a618; **local Lean available** (elan; Mathlib cache ≈ 3 min).
- **Parts 2/5, astrophysics: the Bonnor–Ebert critical sphere PROVED in Work + AUDITED** (`Work/Math/BonnorEbert.lean`): mass increasing to ξ₁ ∈ [6.4507514, 6.4507515], decreasing to 7, m ∈ [1.1822265, 1.1822266], contrast ∈ [14.042032, 14.042033]; 381 kernel-evaluated cells with a new nonlinear cell invariant; blind closure, referee STANDS, 26 printed values screened; candidate C-BE-1 (13.98 printed by Galli et al. 2002).
- LIV experiment in trial: CI artifact `checked-build` + `scripts/restore_checked_build.sh` (branch `wip/checked-build-artifact`).
- CI build artifact landed on main (bf7ef60) after a green trial: restore + `lake build Checked` of main in ≈ 6 min instead of 60–100 min (PROMPT note). Bonnor–Ebert promotion prepared on `wip/be-promo` (build and most trust checks green; four checks left, STATE 0e). Integrity note: one force-push of the run's own wip branch (LEDGER).

## 2026-11-12T0628Z (scheduled run; auditor role 06:28–07:33Z, then LOCK)
- Env: repo ok (add_repo not exposed; detached checkout, unshallowed); LOCK of run 0427Z (alive) → auditor role until its release (f789e4d), LOCK taken 5137574; **local Lean available** (elan); CI artifact `checked-build` restored in ≈ 1 min, new modules built on top in ≈ 5 min (no full build).
- **Parts 2/5: the Bonnor–Ebert critical sphere promoted to Checked** (run 0427Z's branch `wip/be-promo` finished: a new blind literal reading whose template carries its imports, so the Checked copy keeps the reader's code; old second module archived).
- **Part 1: nine hypotheses classified** (`Checked/Trust/NecessityM.lean`) by symmetries of the equations: Bonnor–Ebert fully classified (w(0) = 0 NEEDED by the isothermal scaling u(s) = w(cs) + 2 log c), Gelfand ball 5, Thomas–Fermi 1, Gelfand PDE 2–3. NEEDED 414 → 422, REDUNDANT 117 → 118, open 358 → 349 (against the promotion branch), fully classified 54 → 56 of 155 (Bonnor–Ebert, Gelfand ball).
- PROMPT working notes: read the LOCK line, not just its time (this run duplicated the holder's in-progress promotion locally for ≈ 25 min); a symmetry of the equation witnesses an initial or centre value; a blind-reading template carries its imports.

## 2026-11-12T0828Z (scheduled run)
- Env: repo ok (add_repo not exposed; pre-cloned checkout); local Lean via elan; CI build artifact restored (judge tree in ≈ 3 min). LOCK of run 0628Z → auditor role until 08:41Z, then LOCK.
- Part 3: blind red team AH (Sonnet) on the necessity witness layer: full CI 0/5 valid accepted, the necessity checks alone 4/5. Repairs: `carriesProof` (proof-carrying binder types → `subtype`), set membership split in `partsWalk`, redundancy label across hypotheses and parts (7 headlines relabelled). AFTER: N4 rejects d03–d05. `runs/2026-11-12T0828Z/t5/RESULTS.md`; PROMPT note "Judge the layer under test, not only CI".

## 2026-11-12T1028Z (scheduled run)
- Env: repo ok (add_repo not exposed; pre-cloned checkout); local Lean via elan; CI build artifact restored (75 s; needs `pip install zstandard`). No LOCK at start.
- Parts 2/5: findings F12 (Falkner–Skan separation parameter, Fazio 2012/2020), F13 (five tabulated attached-flow wall shears at β = −0.1988), F14 (Fazio's reverse-flow wall shear) verified, from candidates C-FS-SEP, C-FS-1988, C-FS-1988R; record headlines `Checked.Records.F12_separation`, `F13_wall_shear`, `F14_reversed_wall_shear` (printed − true differences against PRINTED definitions; one new blind reading); certified values 26 → 29.
- CI: main's checked job of f789e4d hung 4 h in its build and held 0e262e6's checked job pending; cancelled; `timeout-minutes: 240` on the checked job (LEDGER, 39.5).


## 2026-11-12T1228Z (scheduled run)
- Env: repo ok (add_repo not exposed; pre-cloned checkout); local Lean via elan; CI build artifact restored by hand (disk-limited). LOCK of run 1028Z alive at start, released minutes later.
- Part 1: 44 hypotheses classified (35 NEEDED, 9 REDUNDANT; open 363 → 319): RK/SRK/PR/PR78 acentric claims (`Checked/Trust/NecessityO.lean`), `b < v_l` redundant in the RK/SRK uniqueness claims (`Checked/Trust/MaxwellRight.lean`: every Maxwell state of a subcritical RK-form isotherm lies right of b), FR13 transition redshift and `eta_ratios` (`Checked/Trust/NecessityP.lean`). RK module doc: a referee sentence calling `b < v_l` essential corrected.
- New blocking check `scripts/trust/check_necessity_prose.py` (N-P1): prose necessity claims cite the generated classification (LEDGER).
- CI: 43196172253 (0e262e6) green on every job → Bonnor–Ebert critical sphere PROVED.

## 2026-11-12T1428Z (scheduled run)
- Env: repo ok; local Lean (elan, Mathlib cache, CI build artifact of 43196172253 restored); CI 43218463622 (4c7b118) in progress, 43235588795 (3aac2e0) pending at start.
- Parts 2/5: attached Falkner–Skan rows β = −0.15, −0.17, −0.18, −0.19, −0.195, −0.198 certified to ten decimals with existence (generator + emitter + generic-K stack; PROVED in Work, axioms standard); referee STANDS-WITH-CORRECTIONS; rows −0.17, −0.18, −0.19 promoted to Checked (`Checked/FalknerSkan/NegWallShearRows.lean`) with a blind β reading of Ganapol 2010 Table 6. −0.195/−0.198: no printed value found (new numbers), Work only.
- Part 1 in the same run: hypotheses 1 and 3 NEEDED in six FS window headlines (`Checked/Trust/NecessityQ.lean`), open 343 → 331. Local replica `local_frozen_step.py --trust 0e262e6` green after two LEDGER disclosure fixes.

## 2026-11-12T1628Z (scheduled run)
- Env: repo ok; local Lean (elan, Mathlib cache, CI build artifact of 43196172253 restored). CI: 43218463622 (4c7b118) checked job cancelled at 240 min — root cause found in its log (axiom-audit's bare `lake build` rebuilt Work on a cache miss) and repaired (`defaultTargets = ["Checked"]`); 43252958184 (156c3da) cancelled as superseded.
- Part 1: `Checked/Trust/NecessityR.lean` — 24 hypotheses of eleven Falkner–Skan headlines classified (13 REDUNDANT: p → 1; 11 NEEDED: p' = q, q > 0); open 331 → 307.

## 2026-11-12T1828Z (scheduled run)
- Env: repo ok; local Lean (elan, Mathlib cache, CI build artifact of 43268238201 restored). CI 43268238201 (6a660ac): checked (strict) green in 64 min and nanoda 4/4 green — run 1628Z's `defaultTargets` repair confirmed; `work` job still running at the end of this run.
- Parts 2/5: reversed-flow Falkner–Skan rows β = −0.15, −0.17, −0.18, −0.19 certified to ten decimals with existence and two decay-class solutions (generator run on the generic-K reversed-flow stack; twelve certificate modules, all compiled first time; PROVED in Work, axioms standard); referee STANDS; Ganapol 2010 Table 7 confirmed to 12 digits at these rows; Stewartson 1954 as quoted by Fazio wrong in the third digit (parked).
- Part 1: `Checked/Trust/NecessityS.lean` — q > 0 NEEDED in the three Ganapol row windows (`fs_neg_wall_shear_17/18/19_window`).
- Records: STATE.md trimmed (older environment lines and summaries moved verbatim to `_archive/STATE_environment_history.md`).

## 2026-11-12T2028Z (scheduled run)
- Env: repo ok; local Lean (elan, Mathlib cache, CI build artifact of 43268238201 restored, run 1828Z's twelve FSRev modules built locally ≈ 15 min). CI 43294811277 (02fb347, run 1828Z's final push) in progress during the run.
- Part 3 by rotation (none since run 0828Z): first blind red team on the verified-findings layer (round AI, Sonnet): **6/6 wrong findings accepted by every check on main** (a correct published value declared wrong, blocks of two findings swapped, a row's β changed, a non-uniqueness theorem called uniqueness, a size word changed, a class qualifier dropped).
- Repair: `scripts/trust/check_findings.py` (FB1–FB6, blocking, 12 controls) — printed values of F12–F14 now bound to Lean statements; the five refuted F13 values are checked mechanically against the certified window. AFTER (not blind): 6/6 rejected plus three judge variants. `check_numbers.py` role of relative differences repaired.

## 2026-11-12T2228Z (scheduled run)
- Env: repo ok; local Lean (elan, Mathlib cache, CI build artifact of 43294811277 restored). CI 43294811277 (02fb347): green on every job → `NegReversedRows` (six headlines) and `NecessityS` PROVED; 43311405425 (50d4d16) in progress.
- Parts 2/5: eleven more reversed-flow Falkner–Skan rows (β = −0.04 … −0.09, −0.11 … −0.14, −0.16) certified to ten decimals with existence, PROVED in Work, referee STANDS (all 19 rows of Ganapol 2010 Table 7 correct to 12 digits; 16 of 19 now machine-checked). New generic tube with free end time (`Checked/FSRev/RTubeA.lean`, `RAssembleA.lean`); 33 certificate modules.
- Records: STATE "Last updated" and environment lines trimmed (oldest moved verbatim to `_archive/STATE_environment_history.md`).


## 2026-11-13T0028Z (scheduled run)
- Env: repo ok; local Lean (elan, Mathlib cache, CI build artifact of 43311405425 restored; run 2228Z's 38 FSRev modules built locally). CI 43311405425 (50d4d16) green on every job; 43333104273 (07b7a68) still running — read next run.
- Parts 2/5: twelve reversed-flow Falkner–Skan rows of Ganapol 2010 Table 7 (β = −0.04 … −0.09, −0.11 … −0.16) promoted to Checked (`NegReversedWallShearRows`), β read blind from the typeset table (Sonnet reader, `SecondReadingFSRevTableRows`); 16 of 19 rows in Checked, PROVED once CI is green.
- Part 3: blind red team AJ on the findings layer, **6/6 wrong findings accepted on main** against FB1–FB6 (all in finding prose no rule reads); repair `check_findings.py` FB7 (finding prose frozen against the CI base, disclosure in LEDGER required); AFTER 0/6 (not blind).
- Records: PROMPT notes (FB7 route; table promotion with a restored CI build); STATE oldest environment line archived.

## 2026-11-13T0228Z (scheduled run)
- Env: repo ok; local Lean (elan, Mathlib cache, CI build artifact of 43333104273 restored). Auditor role until run 0028Z released the LOCK at 02:53Z. CI 43333104273 (07b7a68): green on every job; the run of 7d590d2 still running — read next run.
- Part 1 (rotation): `Checked/Trust/NecessityT.lean` — nine hypotheses NEEDED in four Falkner–Skan headlines (p' = q in the monotone Hiemenz/Homann windows by a shear solving its own linear equation with an integrating factor; `fs_neg_tenth_monotone_lt` 1, 2, 3; `fs_monotone_of_limit` 1, 4, 5, 9 by the certified reversed-flow and Hiemenz solutions and zero-shear profiles); open 304 → 295. `Checked/Trust/NecessityU.lean` — the domain conditions (t ≤ t₀, positive and continuous scale factor) of `lumDistSpec2_pins`, `angDistSpec_pins`, `lumDistFlat_pins`, `comoving_pins` NEEDED (program distances shifted by one off the domain still meet the specifications); `NecessityV.lean` the same for `ricciSpec_pins` 2–4; open → 280, fully classified 56 → 61.
- Parts 2/5: row β = −0.03 of Ganapol 2010 Table 7 frozen (`Work/FalknerSkan/ReversedRowThree.lean` + instantiated blind-restatement closure), referee STANDS (own 40-digit integrator; Ganapol correct to 12 digits), β read blind (row named by its printed wall shear, not its position); certificate chains (degree 14, 26 digits) still generating at the end of the run; promotion script ready.
- Tooling (LIV): `runs/2026-11-13T0228Z/scripts/gen_rev_p.py` + `chain.sh` (progress lines for long chains).
- 2026-11-13T0228Z addendum (after the LOCK was released; run folder only): **row −0.03 chains generated and committed** (`runs/2026-11-13T0228Z/cells/03_{over,slow}.json`, weights w = (2, 8), step 1/64, degree 14, 26 digits; over end margin 5.4e-10, slow 5.4e-12; amplification e^16.8 instead of e^31.6). Root cause of the hours-long chains (LIV): `sqrt_up` in `gen_rev.py` stepped up from the float root by 1/D (D = 10^29), ≈ 10^13 steps per call once the ball grew (py-spy); `runs/2026-11-13T0228Z/scripts/gen_rev_p.py` uses an exact integer square root: each chain now takes < 1 min. With the default weights (1/2, 2) the chains FAIL (end ball 1.6e-6, logs in `cells_failed_w_default/`): the run-0228Z generators would have failed after hours.

## 2026-11-13T0428Z (scheduled run)
- Env: repo ok (add_repo not exposed; pre-cloned checkout, shallow, deepened); local Lean (elan, Mathlib cache, CI artifact `checked-build` of 43333104273 (07b7a68) restored). CI: the runs of 7d590d2, c144ae1, 65920cd, a3f99fd still running during the run (7d590d2's checked job since 03:04Z) — read next run.
- Parts 2/5: row β = −0.03 of Ganapol 2010 Table 7 proved in Work (statement of run 0228Z's freeze unchanged, axioms standard) and promoted to Checked (`fs_neg_reversed_wall_shear_3_exists` in `NegReversedWallShearRows`; β read blind by run 0228Z); 17 of 19 rows are Checked statements.
- Tooling (LIV): root cause of the hour-long certificate chains — the generators' `sqrt_up` walked from the float root in steps of 10⁻²⁹ (≈ 10¹³ steps per call); exact integer square root (`runs/2026-11-13T0428Z/scripts/gen_rev_q.py`): a 324-cell chain in < 1 min (run 0228Z's session found the same in parallel). PROMPT note: exact roots, try weights before precision.
- Records check (LIV): a3f99fd's STATE status line fails check_status_lines S2 (written after run 0228Z's replica); reworded; new `scripts/trust/records_check.py` (every Lean-free CI command on the records as they stand, ≈ 1.5 min) and PROMPT note to run it before every final push.
- Rows −0.02, −0.01: with the q-clamp at 4 (`gen_rev_wide.py`) all three chains of −0.02 pass, and over and slow of −0.01; the tube of −0.01 does not yet; the Lean stack needs the wider clamp (`runs/2026-11-13T0428Z/wide/`).

## 2026-11-13T0628Z (scheduled run)
- Env: repo ok (add_repo not exposed; pre-cloned checkout reset to origin/main 1d5362b); local Lean (elan, Mathlib cache, CI artifact `checked-build` of 43354856508 (7d590d2) restored; incremental build of main ≈ 30 min). CI: the runs of 5983bfe (checked job) and 94ff806 (pending) still running during the run — read next run.
- Parts 2/5: the last two rows of Ganapol 2010 Table 7 (β = −0.02, −0.01) frozen, refereed (STANDS), β read blind, proved in Work and promoted to Checked (`fs_neg_reversed_wall_shear_2_exists`, `fs_neg_reversed_wall_shear_1_exists`): all 19 rows of the table are Checked statements. Route: a parallel stack with the shear clamp as a parameter (`Checked/FSRevW/`, ported by asserted replacements, every module compiled first time), clamp 4.
- Tooling (LIV): row −0.01's tube failed at every step size with weights (4, 32); balancing the scaled off-diagonal entries of the weighted Jacobian (best one-sided bound ≈ (K|q|/8)^{1/3}) gave w = (512, 24), amplification e^7.3 instead of e^20+; PROMPT note.

## 2026-11-13T1028Z (scheduled run)
- Env: repo ok (add_repo not exposed; pre-cloned checkout reset to origin/main 4af3d97); local Lean installed (elan, Mathlib cache) but not needed (Python and records only); auditor role all run (LOCK of run 0828Z, heartbeat 09:38Z). CI: 94ff806 (43373750289) red only at StatementDeps (a cited non-headline `core_rev`, gone on main since); 5c06d2e running.
- Part 3: blind red teams AK (main 4af3d97) and AL (against the repair) on new or disclosed verified findings, disclosure allowed: 6/6 and 6/6 wrong findings accepted. Repair `scripts/trust/check_findings.py` FB8 (record of its own; every heading `### F<k>`), FB9 (generated Correct line, `--write-correct`); AK 1/6, AL 5/6 after (not blind). `runs/2026-11-13T1028Z/t5/RESULTS.md`.
- LOCK of run 0828Z (heartbeat 09:38Z) taken over at 12:08Z (48.4, 150 min, no push); its compiled part-1 scratch is STATE 0g.
- Next: promote run 0828Z's scratch (STATE 0g); blind-reader route for Scope/Printed lines of findings (STATE 0f).

## Necessity: run 0828Z's scratch promoted, RK existence co-volume (run 2026-11-13T1522Z)
- New `Checked/Trust/MaxwellRightVdW.lean`, `MaxwellRightPR.lean`, `NecessityEta.lean` (run 0828Z's compiled scratch, module docs reworded without decimals/fractions for check_prose rule 7) and `NecessityW.lean` (`rk_coexistence_exists_h3`); `necessity_open_baseline.txt` 92 → 86 lines; TRUST_MAP open 280 → 267, fully classified 61 → 63.
- LOCK of run 1228Z (no push for 177 min) taken over; CI 43422957898 (028d5c4) read green on every job.
- Next: CI read of this push; then by rotation parts 2/5 or 3 (STATE 0f).

## 2026-11-13T1640Z (scheduled run)
- Env: repo ok (add_repo not exposed; checkout reset to origin/main ad2a969); local Lean (elan, Mathlib cache, CI build artifact of 028d5c4 restored); CI 43462297471 (c5c2a35) still running at the end — read next run.
- Parts 2/5 by rotation: attached Falkner–Skan rows β = −0.13, −0.14, −0.16 (Ganapol 2010 Table 6) blind β reading, generated chains, freeze 67f8eef, referee STANDS, PROVED in Work (f62e1b2); promoted with run 1428Z's row −0.15 to `Checked/FalknerSkan/NegWallShearRowsTop.lean` (eight headlines): every row of Table 6's decelerating segment is a Checked statement (PROVED once CI is green).
- Part 1 in the same run: `Checked/Trust/NecessityX.lean` — hypotheses 1, 3, 7 NEEDED and 6 REDUNDANT in the four new windows (7 by the reversed-flow headline of the same row).
- PROMPT note: count table rows by a property visible in the whole table; referee reports come back as text.

## 2026-11-13T1828Z (scheduled run)
- Env: repo ok (add_repo not exposed; checkout reset to origin/main cc5a1da); no local Lean needed (Python only; `.lake` outputs from the author-files artifact of 028d5c4); CI 43462297471 (c5c2a35) and 43482419250 (7911453) still running — read next run.
- Part 3 by rotation (STATE 0f, changed approach after four word-rule rounds): `check_findings.py` FB10/FB11/FB12 — the trusted part of a verified finding (Printed and Correct lines, certified blocks) is generated, author prose labelled under a fixed marker, headings labelled as the author's title; `FINDINGS.md` F1–F14 relaid out without rewording.
- Blind red team AM: 6/6 accepted against the first version; repairs (not blind) → 2/6 (both headings). Selftest controls 29 → 45.
- Next: CI read; part 3 later: generate headings, reader files for pre-route readings, records for F4–F7.

## 2026-11-13T2028Z (scheduled run)
- Env: repo ok (add_repo not exposed; checkout reset to origin/main 36d2a3d); local Lean (elan, Mathlib cache, CI build artifact of c5c2a35 restored); CI 43462297471 (c5c2a35) green on every job; 7911453's checked job cancelled (superseded); 36d2a3d pending.
- Part 1 by rotation: `Checked/Trust/NecessityY.lean` (generated, `runs/2026-11-13T2028Z/scripts/gen_necY.py`) + `Checked/FSRev/RFlowCells.lean` — f(0) = 0 and p(0) = 0 NEEDED in the seven attached-row windows β = −0.13 … −0.19, in `fs_neg_wall_shear_window` and in `F13_wall_shear` (18 classifications; open 279 → 261): translates of the reversed-flow solution of the same β, located by its tube's certified cells (sub-cell Taylor shift at −0.1988).
- CI repair: StatementDeps' citation registry exempts the agreement theorems of `Checked.Trust.Transcriptions` (cited by run 1828Z's generated Printed lines; every push since af2cc09 would have failed the trust step); `precheck_citations.py` mirrors it and now runs in `records_check.py`.
- Next: CI read; then parts 2/5 or 3 by rotation; hypothesis 8 of the nine needs an algebraically decaying attached solution.

## 2026-11-13T2228Z (scheduled run)
- Env: repo ok (add_repo not exposed; checkout reset to origin/main 3cd85d2); local Lean (elan, Mathlib cache, CI build artifact of c5c2a35 restored in 36 s; incremental `lake build Checked` ≈ 9 min); CI 43511962008 (3cd85d2) in progress all run (checked job started 21:59Z).
- Parts 2/5 by rotation: **the Bonnor–Ebert critical mass is the strict maximum of the pressure-confined mass over every radius** — frozen, proved in Work in ≈ 25 min (Volterra's Lyapunov function in homology variables + convex-duality bound; state at radius 7 from the existing certified cells), blind restatement closed, referee STANDS, promoted (`Checked.Math.BonnorEbertMax.bonnor_ebert_max`, NV, literal readings, all five hypotheses classified in `Checked/Trust/NecessityZ.lean`).
- Next: CI read; then parts 1 or 3 by rotation.

## 2026-11-14T0028Z (scheduled run)
- Env: repo ok (add_repo not exposed; checkout reset to origin/main 8e3a22d); local Lean (elan, Mathlib cache, CI build artifact of c5c2a35 restored; `lake build Checked` green; StatementDeps exit 0, tree clean). CI 43511962008 (3cd85d2) green on every job → Ganapol Table 6 rows −0.13 … −0.16 PROVED; 43528111166 (8e3a22d) checked job running at the end.
- Part 3 by rotation: FB13 generates the heading of every verified finding (author titles moved unchanged into the notes; validation packet unchanged). Blind red team AN (Sonnet) against it: 6/6 accepted by the findings rules (5/6 by all of CI), all through the frame around the generated part; repairs FB14 (fixed frame, generators read only generated blocks, notes cannot render as structure) and FB15 (registry phrases) → 0/6 (not blind). Selftest 45 → 62 controls. PROMPT note on frame attacks.
- Next: CI read; then part 1 or parts 2/5 by rotation; part 3 later: a blind round against FB14/FB15, reader files for the pre-route readings, records for F4–F7.

## 2026-11-14T0228Z (scheduled run)
- Env: repo ok (add_repo not exposed; checkout reset to origin/main 89c8b4e); local Lean (elan, Mathlib cache, CI build artifact of 3cd85d2 restored; `lake build Checked` green; StatementDeps exit 0). CI 43528111166 (8e3a22d) checked job still building at the end; 89c8b4e's run pending (superseded by this run's push, which contains it).
- Part 1 by rotation: `Checked/Trust/NecessityAA.lean`, `NecessityAB.lean` (+ `Checked/FSNeg/LFlowCells.lean`) — 26 hypotheses NEEDED in `fs_neg_decay_max_shear`, `fs_neg_decay_equal`, the separation pair (`fs_separation_equal`, `fs_separation_below_printed`, `F12_separation`) and `fs_neg_reversed_printed_overshoots`: translates of the Checked reversed-flow solution of row β = −0.13 (no new certificates), the attached solution of the row, explicit fast-approach profiles; `fs_neg_tenth_window` 4, 5 and `fs_neg_tenth_monotone_lt` 5 by translates of the β = −1/10 reversed solution (older cells ported). Open 261 → 235.
- Next: CI read; then parts 2/5 or 3 by rotation; part 1 later: algebraic-approach attached solution, separation profiles with transpiration.

## 2026-11-14T0428Z (scheduled run)
- Env: repo ok (add_repo not exposed; checkout reset to origin/main 0935097); local Lean (elan, Mathlib cache, CI build artifact of 8e3a22d restored; `lake build Checked` green; StatementDeps relock). CI 43528111166 (8e3a22d) green on every job → `bonnor_ebert_max` PROVED (Alexander told); 43551580603 (0935097) in progress for the whole run.
- Parts 2/5 by rotation: **the first minimum of the Bonnor–Ebert mass** — frozen, proved, blind restatement closed, referee STANDS, promoted (`Checked.Math.BonnorEbertMin.bonnor_ebert_min`: ξ₂ ∈ [67.0075, 67.0076], m ∈ [0.694366, 0.694367], contrast ∈ [2579.69, 2579.71], strict minimum over [ξ₁, S]; NV, literal readings, all five hypotheses classified in `Checked/Trust/NecessityAC.lean`). New validated cell scheme in homology variables (`Checked/Math/BEHCell.lean`, growth like a power of the radius), 156 cells on [7, 150], Volterra tail from below.
- Next: CI read; then part 3 or part 1 by rotation; parts 2/5 later: the second maximum and the whole spiral with the same cells.

## 2026-11-14T0628Z (scheduled run)
- Env: repo ok (add_repo not exposed; checkout reset to origin/main 96643b0); local Lean (elan, Mathlib cache, CI build artifact of 8e3a22d restored; `lake build Checked` green; StatementDeps relock, Claims). CI 43551580603 (0935097) checked job still building during the run; 43563791919 (96643b0) in progress from 07:05Z; this run's push queued behind it.
- Part 3 by rotation: **every verified finding has a Lean record** — `Checked.Records.F4_values`, `F5_values`, `F6_third`, `F6_fourth`, `F7_third`, `F7_fourth` (printed and corrected y-series coefficients in de Sitter through the pinned `decel`, `cosmoCoeff`, `omega0` and the PRINTED formulas; no hypotheses, no literal needing a reading); FINDINGS F4–F7 regenerated (heading, Printed, Correct, certified blocks); `findings_norecord_baseline.txt` empty.
- Next: CI read; then part 1 or parts 2/5 by rotation; part 3 later: fresh blind readings with reader files for the legacy PRINTED definitions.

## 2026-11-14T0828Z (scheduled run)
- Env: repo ok (add_repo not exposed; checkout reset to origin/main aaa5d26); local Lean (elan, Mathlib cache, CI build artifact of 0935097 restored; `lake build Checked` green; StatementDeps relock, Claims). CI 43563791919 (96643b0, `bonnor_ebert_min`) still in its checked job for the whole run; 43572789731 (cb49239) pending behind it.
- Part 1 by rotation: **smoothness NEEDED in the eleven past-only printed-coefficient cosmography headlines and in `lookback_second_order_bigO`** (`Checked/Trust/NecessityAD.lean`): kinked scale factors whose junk top derivative makes the printed coefficient right on the past side. Also both derivative hypotheses of the `decel` pin (`Fidelity.decelSpec_pins` 2, 3) NEEDED. Open 235 → 221; thirteen more headlines fully classified (65 → 78).
- CI read at the end: 43563791919 (96643b0) green on every job → `bonnor_ebert_min` PROVED (Alexander told).
- Next: CI read of c3ca8a4; then parts 2/5 or 3 by rotation; part 1 later: the two-sided companions (oscillating witness), algebraic-approach attached solution, separation profiles with transpiration.

## 2026-11-14T1028Z (scheduled run)
- Env: repo ok (add_repo not exposed; checkout reset to origin/main 48e6826); local Lean (elan, Mathlib cache, CI build artifact of 96643b0 restored; `lake build Checked` green; StatementDeps relock). CI at the start: 43579906667 (4a73412) and 43572789731 (cb49239) in their checked jobs, 43581569718 (c3ca8a4) pending.
- Parts 2/5 by rotation: **the second maximum of the Bonnor–Ebert mass** — frozen, proved, blind restatement closed, referee STANDS, promoted (`Checked.Math.BonnorEbertMax2.bonnor_ebert_second_max`: ξ₃ ∈ [733.5, 734], m(ξ₃) ∈ [0.8306, 0.8308], contrast ∈ [258300, 258800], strict maximum over [ξ₂, S] for every S ≥ 2000; NV, literal readings, all five hypotheses classified in `Checked/Trust/NecessityAE.lean`). 131 homology cells on [150, 2000], Volterra tail from above.
- Next: CI read; then part 3 or part 1 by rotation; parts 2/5 later: the second minimum with a tighter start.

## 2026-11-14T1228Z (scheduled run)
- Env: repo ok (add_repo not exposed; checkout reset to origin/main 20252cb, unshallowed mid-run); local Lean (elan, Mathlib cache, CI build artifact of 96643b0 restored after installing a zstd decompressor; `lake build Checked` green; StatementDeps exit 0, Claims, tree unchanged). CI 43581569718 (c3ca8a4) green on every job (13:46Z); 43590961602 (071b543) in its checked job at the end.
- Part 3 by rotation: blind red team AO (Sonnet) against FB10–FB15 of the findings layer: 4/4 valid wrong findings accepted by every Python check (2 more out of scope), all through the generators' inputs (author-written class phrases; a U+2028 parser differential), none through the fixed frame. Repairs `check_findings.py` FB16 (one line splitter, no other line-break character), FB17 (class phrases plain text; new ones copied from blind readings, brief → reading → copy; planted controls in `route_control.py`), FB18 (fixed reading guide); `make_packet.py` labels the Source line unchecked; `restore_checked_build.sh` installs zstandard. AFTER 6/6 caught (not blind). PROMPT note: inputs of generated lines.
- Next: CI read (071b543: `bonnor_ebert_second_max`); then part 1 or parts 2/5 by rotation; part 3 later: a blind round against FB16–FB18, reader files for the pre-route readings.

## 2026-11-14T1428Z (scheduled run)
- Env: repo ok (pre-cloned detached checkout; `git checkout -B main origin/main`); local Lean via elan + restored `checked-build` of c3ca8a4; CI 43590961602 (071b543) checked job running for the whole run.
- Parts 2/5 and 1: one-sided cells in a weighted norm (`Checked/Math/BEOCell.lean`) — the validated Bonnor–Ebert enclosure contracts (8·10⁻⁷ → 1·10⁻⁷ on [150, 20000]); LEDGER experiment of run 1028Z confirmed.
- New headline `Checked.Math.BonnorEbertMin2.bonnor_ebert_second_min` (second minimum of the Bonnor–Ebert mass: ξ₄ ∈ [7849.5, 7849.75], m ∈ [0.787992, 0.787995], contrast ∈ [31193900, 31196100], strict minimum over [ξ₃, S]); frozen → Work proof → blind closure → referee STANDS → Checked with NV witness, literal readings, NecessityAF (fully classified).


## 2026-11-14T1628Z (scheduled run)
- Env: repo ok (pre-cloned shallow detached checkout; `git checkout -B main origin/main`, unshallowed); local Lean via elan + restored `checked-build` of c3ca8a4; disk allowance filled once (freed: Mathlib cache tarballs, stale check scratch repos). CI 43590961602 (071b543) green on every job at 16:40Z → `bonnor_ebert_second_max` PROVED; 43611102762 (fc559f2) in progress at the end. Alexander asked live for a status summary (answered).
- Part 3: fresh blind readings (readers download the arXiv PDFs themselves) for the 13 pre-route PRINTED definitions behind F3–F7, F9, F10; 13 agreement theorems repointed, all closed by `ring` first time; FINDINGS headings/Printed lines regenerated: undescribed printed values 13 → 0. The Sec. X brief tripped check_brief_leak L3 (equation numbers and arXiv id contain coefficient digits): reading redone from a second brief, rule unchanged.
- Blind red team AP (Sonnet) against FB10–FB18: 5 valid wrong findings accepted (4 rendering/look-alike differentials in the notes, 1 forged route); LEDGER experiment of run 1228Z survives. Repairs `check_findings.py` FB19 (notes = one-line author bullets, no HTML), FB20 (alphabet and format-character rule; generated marks matched on a folded copy), one-dash setext underline; 8 controls.
- Next: CI read (fc559f2: `bonnor_ebert_second_min`); then parts 2/5 or part 1 by rotation.
