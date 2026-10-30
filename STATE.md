# STATE

Last updated: 2026-10-30, run 2026-10-30T0430Z (scheduled).

## Phase
S1, S2 DONE. Working target 1 (cosmography). Verified findings F1, F2.

## Target 1: Cosmography: low-redshift (Hubble-series) expansions in FLRW
Case and the eight items: `TARGETS.md` #1 (unchanged).
Bottleneck now: remaining typeset-confirmed candidates C3 (lookback-distance series, de Sitter) and C1 (d_Q y² coefficient), and widening the screen. Pipeline (screen → typeset → Lean → audit → referee) now proven twice; witness models no longer need closed forms (`exists_local_model`).

## Results (statuses, annex XXXVIII)
- **PROVED** `Checked.Cosmography.lookback_second_order`, `..._bigO`: run 0028Z.
- **PROVED** (F1) `Checked.Cosmography.Aviles.flatLCDM_coeffs`, `avilesL0Claim_false`, `avilesM0Claim_false`, `AvilesWitness.printedL0_false_at`, `printedM0_false_at`: run 0220Z.
- **PROVED** (F2) `Checked.Cosmography.CPL.flatCPL_coeffs` (flat matter + CPL: q₀, j₀, s₀, l₀ for every Ω, w₀, wₐ; C⁵ at t₀), `printedL0_ne`, `clsL0Claim_false` (model Ω=0, w₀=−1, wₐ=2/3, a = 1 − log(1−t)). Audit `runs/2026-10-30T0430Z/audit.md`. CI 41007523313 green (build, leanchecker, axiom-audit, nanoda 336194 decls).
- **PROVED** `Checked.Cosmography.CPLExistence.exists_flatCPL`, `printedL0_false_at`, tool `exists_local_model` (commit b6267ff, CI 41007796446 green: build, leanchecker, axiom-audit, nanoda 374957 decls). The printed CPL l₀ is now refuted at every parameter point with (1−Ω)(7−Ω)wₐ ≠ 0.
- **Finding F2** (FINDINGS.md): verified; referee STANDS-WITH-CORRECTIONS; reported to Alexander this run.
- Candidates C1, C3: typeset-confirmed as printed and wrong (sympy). Need Lean evidence.

## Environment (this run)
- Repo pre-cloned in the session (add_repo not exposed as a tool; not needed). Pushes verified (remote head = local each time).
- Local Lean: elan + `lake exe cache get` (~3 min); CPLCoefficients elaborates in ~90 s.
- arXiv PDFs via curl; e-print robots-blocked (unchanged).

## Daily review (53.3), 2026-10-30
- AUDITED + PROVED headlines in last 24 h: 2 (0028Z) + 5 (0220Z) + 5 (0430Z). Findings: F1, F2 verified.
- Bottleneck history: C1–C4 candidates since run 0028Z; two of four now verified findings.
- Patterns fixed this run: witness hunting (→ ODE existence tool); non-polynomial laws (→ auxiliary function + generator). LEDGER experiments.

## Known gaps
- Cosmetic linter warnings in generated proofs (unused simp args / push_cast). Leave.
- Import closure grew (ODE module): nanoda step 8 min in CI 41007796446 (was 4.5). Watch; if CI > 20 min, split heavy imports out of Checked's root or run nanoda per module.

## Open questions for Alexander
None. F2 sent as information (any contact with authors is his call, 47.1).

## Exact next step
1. Read CI for this run's last commits by ID (records only, after 41007796446).
2. C3 (Capozziello, Cardone, Salzano 2008, arXiv:0802.1583v2 App. A, Eq. A2): D(z) = (cz/H₀)[D⁰ + D¹z + … + D⁴z⁴] is the lookback distance D = c(t₀ − t*) re-expanded in z; printed D⁴ (z⁵ coefficient) has (7/2)q₀⁴ and −l₀/120 wrong. De Sitter (a = e^{H₀t}: q₀ = −1, j₀ = s₀ = l₀ = 1) has D = (c/H₀)ln(1+z) exactly, so D⁴ = 1/5, printed 2.825. Formalization plan (avoids inverting z(t)): claim "for every C⁶ a with H₀ > 0, (t₀ − t) − (1/H₀)Σ_{k≤4} Dᵏ z(t)^{k+1} = O((t − t₀)⁶)"; refute on de Sitter using Mathlib's log series bound (`Real.abs_log_sub_add_sum_range_le`) and that z ≍ H₀(t₀ − t), so a nonzero z⁵ term cannot be O(z⁶). Freeze first; blind-restate (the "O" reading is Underspecified — record it).
3. C1 (Cattoën–Visser 2007 Eq. 59, d_Q y² coefficient 1/12 vs 1/24): find the simplest model where the coefficient is checkable (de Sitter or EdS closed-form d_Q(y)); same iteratedDeriv approach.
4. Widen the screen with the typeset route (Pourojaghi et al. 2408.10704, D'Agostino–Nunes 2307.13464, Li–Du–Xu 1903.11433, and papers citing CLS 2011 / Bamba et al. 2012 that reprint CPL cosmographic coefficients — the F2 formula may propagate further).
Blocking: nothing.
