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
- Metric: physics headlines resting only on pinned definitions 63/82 (start ≤ 15/88); pinned definitions 12 (start 4).
- PROMPT notes: blind-spec → verbatim core → meets → pin-by-general-law protocol; trust map usage. LEDGER: experiment (trust map), evaluation of run 1828Z experiments.
