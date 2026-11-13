# Run 2026-11-13T0428Z

Scheduled run. LOCK 7755b69 (04:29Z) → removed in the final commit.

**THE RESULT:** parts 2/5 (and tooling, annex LIV). (1) Row β = −0.03 of Ganapol 2010 Table 7 is proved in Work (`Work/FalknerSkan/ReversedRowThree.lean`, statement of run 0228Z's freeze 41e05bf unchanged, axioms standard) and promoted to Checked as `fs_neg_reversed_wall_shear_3_exists` (`Checked/FalknerSkan/NegReversedWallShearRows.lean`, certificates `Checked/FSRev/RThree{Over,Slow,Tube}.lean`, β read blind by run 0228Z): 17 of the table's 19 rows are Checked statements, PROVED once CI is green on every job. (2) The reason certificate chains took hours is found and fixed: the generators' `sqrt_up` stepped up from the float root by 10⁻²⁹ (≈ 10¹³ steps per call once the error ball passed 10⁻⁸); with `math.isqrt` a 324-cell chain takes under a minute. (3) The last two rows (−0.02, −0.01) are feasible on the generator side with the q-clamp widened to 4; the Lean stack still clamps at 2.

**What can a scientist now trust without checking it themselves, that they could not before?** The reverse-flow wall shear of the Falkner–Skan boundary layer at β = −0.03, −0.0825629652 < f''(0) < −0.0825629651, together with the existence of a solution in the stated class, as a Checked statement whose β was read blind from the published table (CI pending).

**Weakest unchecked step:** the run's Checked promotion is judged by the local CI replica only until CI finishes; CI has not yet finished on runs 0028Z/0228Z's pushes (the twelve earlier rows, NecessityT/U/V). Rows −0.02, −0.01 are not proved.

## Steps
1. Chains: run 0228Z's chain driver restarted at 04:28Z; the progress lines stopped at cell 112, and py-spy showed `sqrt_up` (line 54). Patched copy `scripts/gen_rev_q.py` (exact integer root, least s = k/D with s² ≥ x; asserted). Degree 14 / 26 digits / weights (1/2, 2) FAILED (end ball 1.6·10⁻⁶ against a margin of 5·10⁻¹⁰, amplification e^31.6); parallel trials in seconds chose over 64/18/30 and slow 64/20/32 (logs `cells/`). Tube: run 2228Z's chain (copied).
2. Certificates emitted by `runs/2026-11-12T2228Z/scripts/emit_rows.py`, module docs name this generator; compiled first time (≈ 9 min each, two at a time). `make_row3.py prove`: diff = imports, four helper lemmas, proof. Axioms standard. Blind closure builds sorry-free.
3. Promotion by `runs/2026-11-13T0228Z/scripts/promote_row3.py` (+ module doc names `ReversedRowThree.lean`; LEDGER). Relock, TRUST_MAP, CLAIMS, packet.
4. Run 0228Z's session, still alive, found the same root cause in parallel and committed cheaper chains (weights (2, 8), degree 14, 26 digits) to its own folder at 04:40Z, after these were compiled. Lesson in PROMPT: try weights before precision.
5. Rows −0.02, −0.01 (`scripts/gen_rev_wide.py`, `FS_QCLAMP`; logs `wide/`): row −0.02 passes on all three chains with the clamp at 4 (w = (4, 32), step 1/128, degree 16, 30 digits; tube end time 3/2); row −0.01: over and slow (degree 18, 36 digits) pass, the tube not yet (μh ≥ 1 at step 1/256 with clamp 5–6; q + B above clamp 4).

## Verification
- Local: see the final commit message (CI replica against 07b7a68, the newest fully green ancestor).
- CI: read next run.
