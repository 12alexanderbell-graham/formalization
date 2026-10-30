# Run 2026-10-30T0430Z (scheduled)

**TARGET AND BOTTLENECK:** target 1 (cosmography). Bottleneck: Lean evidence for C4 (CLS 2011 Eq. 22, CPL l₀), the candidate with most practical weight (CPL is the standard dynamical-dark-energy fit). Yes → second verified finding, in a formula reprinted in a widely cited review; no → drop C4.

**WHAT WE ACTUALLY DID:** froze statements (4663ac9); proved the general flat matter + CPL coefficients q₀…l₀ (sympy-generated two-identity system, ~2 local iterations); explicit closed-form witness (Ω = 0, a = 1 − log(1−t)); blind restatement closed in Lean both ways; referee; existence of CPL models at every parameter point via Mathlib Picard–Lindelöf; promoted to Checked.

**RESULT:** **F2 verified.** PROVED + AUDITED (Checked): `Checked.Cosmography.CPL.flatCPL_coeffs`, `printedL0_ne`, `clsL0Claim_false`, `Checked.Cosmography.CPLExistence.exists_flatCPL`, `printedL0_false_at`. CI IDs in STATE/LEDGER.

**ACTUAL IMPROVEMENT:** second verified finding; the printed CPL l₀ (missing factor 9) refuted at every parameter point with wₐ ≠ 0, Ω ≠ 1; error also in Bamba et al. 2012 review Eq. (11.38). Paper's own numbers/figures unaffected (Fig. 2 follows the correct value). New reusable tool: local model existence for any smooth expansion law.

**WHAT COULD STILL BE WRONG:** blind restater, referee and main session are the same model (shared blind spots); scope judgement for Fig. 2 rests on the referee's recomputation and a visual read of the published curve crossing (≈1.35).

**STILL MISSING / NEXT STEP:** see STATE (C3, C1; widen screen; check who else reprints the CPL l₀).

Files: `audit.md`, `source_C4.md`, `C4_blind.lean`, `C4_blind_sympy.py`, `typeset/`, `referee/` (referee scripts), `scripts/` (`truth.py`, `gen_cpl.py`, Lean fragments).
