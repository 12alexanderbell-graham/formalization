# STATE

Last updated: 2026-10-30, run 2026-10-30T0220Z (scheduled).

## Phase
S1, S2 DONE. Working target 1 (cosmography). First verified finding F1.

## Target 1: Cosmography: low-redshift (Hubble-series) expansions in FLRW
Case and the eight items: `TARGETS.md` #1 (unchanged; see previous STATE in git for the full list).
Bottleneck now: turning the three typeset-confirmed candidates (C1, C3, C4) into Lean evidence, and widening the screen now that the pipeline (screen → typeset → Lean → audit → referee) is proven end to end on F1.

## Results (statuses, annex XXXVIII)
- **PROVED** `Checked.Cosmography.lookback_second_order` (o(z²)) and `..._bigO` (O(z³)): run 0028Z.
- **PROVED** `Checked.Cosmography.Aviles.flatLCDM_coeffs`: flat ΛCDM, any Ω, C⁶ at t₀: q₀ = 3Ω/2 − 1, j₀ = 1, s₀ = 1 − 9Ω/2, l₀ = 1 + 3Ω + 27Ω²/2, m₀ = 1 − 27Ω/2 − 81Ω² − 81Ω³/4. Audit `runs/2026-10-30T0220Z/audit.md`; CI 40996176398 green; nanoda passed on CI 40996270496.
- **PROVED** `Checked.Cosmography.Aviles.avilesL0Claim_false`, `avilesM0Claim_false` (printed Eq. 15 refuted on Einstein–de Sitter). Same audit and CI.
- **PROVED (CI pending at record time, see below)** `Checked.Cosmography.AvilesWitness.printedL0_false_at` (every Ω ∈ (0,1)), `printedM0_false_at` (every Ω ∈ (0,1) except (√7−1)/3), via `exists_flatLCDM` (sinh^{2/3} witness). Audit addendum. Commit 8f62c67, CI run 40997210361; then 40997256530 (nanoda blocking).
- **Finding F1** (FINDINGS.md): verified; referee STANDS-WITH-CORRECTIONS; nanoda repaired. Reported to Alexander this run.
- Candidates C1, C3, C4: typeset-confirmed as printed and wrong (sympy; C4 twice independently). Not findings yet: Lean evidence, audit, referee to do.

## Environment (this run)
- Repo reachable; pushes verified (remote head = local each time).
- Local Lean: elan + `lake exe cache get` work (~3 min); full build ~1 min.
- Local build of external tooling (lean4export, nanoda) refused by the environment's safety classifier: test tooling via CI.
- arXiv PDFs downloadable with curl; `arxiv.org/e-print/` is robots-blocked (do not use mirrors).
- nanoda: repaired (lean4export v4.35.0 + nanoda_lib 8de7e0c), blocking again from commit 30112b9.

## Daily review (53.3), 2026-10-30
- AUDITED + PROVED headlines in last 24 h: 2 (run 0028Z) + 5 (run 0220Z). Findings: 1 verified (F1), 3 typeset-confirmed candidates.
- Pattern fixed this run: summariser transcription made every screen hit unverifiable → typeset route in PROMPT (LEDGER experiment). Tooling gap (nanoda) closed.

## Known gaps
- If CI 40997210361 or 40997256530 is red, fix that first (the witness file and the blocking nanoda step were green locally / in the previous CI respectively).

## Open questions for Alexander
None. F1 sent as information (whether to contact the authors is his call, 47.1).

## Exact next step
1. Check CI 40997210361 and 40997256530 by run ID; if red, fix first.
2. C4 (Capozziello, Lazkoz, Salzano 2011 Eq. 22, CPL l₀): Lean theorem for the correct l₀ of flat matter+CPL. Method (worked out, not yet coded): auxiliary functions x(t) = a(t)^p with p = −3(1+w₀+w_a) and y(t) = exp(−3w_a(1 − a(t))). Then the squared law is polynomial: a·ȧ² − Ω a₀³… (normalise a₀ via ratios) − (1−Ω)·a³·x·y = 0 near t₀, plus exact chain-rule identities a·ẋ − p·x·ȧ = 0 and ẏ − 3w_a·y·ȧ = 0. Extend `gen.py` to a system: differentiate all three zero-functions repeatedly with `step`, unknowns a_k, x_k, y_k, solve at t₀ (x = y = 1 there if a₀ = 1; otherwise carry a₀^p). Then refute the printed w_a² term: needs a model with w_a ≠ 0 and Ω_m < 1; existence via an ODE existence theorem (Mathlib `IsPicardLindelof`) or state the refutation conditional on existence and record it as PROVED-CONDITIONAL. Why: C4 is the candidate whose error matters most for current CPL fits.
3. Then C3 (de Sitter, ln(1+z) z⁵ coefficient) and C1 (d_Q y² coefficient; needs M3 d_L to O(z³)).
4. Widen the screen (9 papers so far) with the typeset route: other ΛCDM / wCDM / CPL cosmographic coefficient tables (e.g. Pourojaghi et al. 2408.10704, D'Agostino–Nunes 2307.13464, Li–Du–Xu 1903.11433).
Blocking: nothing.
