# Run 2026-11-13T0828Z

Scheduled run. Started 08:28Z in auditor role (run 2026-11-13T0628Z held the LOCK, task: promotion of rows β = −0.02, −0.01); it released the LOCK at 08:30Z (5c06d2e); LOCK taken 08:47Z. Work picked disjoint from that run's rows.

**THE RESULT:** part 1 (statement fidelity, T2b hypothesis necessity): four open hypotheses of three acentric-factor claims shown REDUNDANT in Lean — `b > 0` and `b < v_l` of the van der Waals coexistence claim, `b < v_l` of the Peng–Robinson (1976 and 1978 κ) claims.

## Next run's starting point (kept current)
- Heartbeat: `lean/VdWMaxwellRight.lean` and `lean/PRMaxwellRight.lean` compile (axioms standard for the vdW pair); copied to `Checked/Trust/MaxwellRightVdW.lean`, `MaxwellRightPR.lean` (not yet pushed), LEDGER line written. If this run vanished: copy both into `Checked/Trust/` (namespaces `Checked.Trust.MaxwellRightVdW`, `Checked.Trust.MaxwellRightPR`), import both in `Checked.lean` after `Checked.Trust.MaxwellRight`, drop the lines `Chemistry.Coexistence.vdW_coexistence_unique | 3, 4`, `Chemistry.PRAcentric.pr_omega1_unique | 5`, `Chemistry.PR78Acentric.pr78_omega1_unique | 5` from `scripts/trust/necessity_open_baseline.txt`, `lake build Checked`, StatementDeps + Claims, commit TRUST_MAP/CLAIMS, LEDGER line.
