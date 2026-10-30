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
- Env: repo ok (pre-cloned); local Lean via elan ok; previous CI 41036605782, 41037683712 green; this run's CI in STATE.
- **Verified finding F6** (Bamba et al. 2012 Eqs. 10.55–10.57, verbatim from Capozziello & Salzano 2009 Eqs. 56–58: curvature terms of D³_{L,y}, D⁴_{L,y} wrong; flat parts right). PROVED + AUDITED in Checked: general curved d_L(y) to y⁵ for every real K and every C⁵ scale factor; refutations (general conditions, a = eᵗ with K = 1, Milne). Blind restatement closed in Lean; referee STANDS-WITH-CORRECTIONS.
- F4 provenance corrected (sign error already in 0902.0088 Eq. 55). New candidates C9, C10 (referee side checks); C7 third route.
- New tool: truncated-series algebra (`approx_mul`, `approx_pow`). PROMPT notes: approx algebra; `unfold` order; referee file hygiene.
- Message to Alexander: F6 (L.2).

