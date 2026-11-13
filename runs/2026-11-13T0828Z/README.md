# Run 2026-11-13T0828Z

Scheduled run. Started 08:28Z in auditor role (run 2026-11-13T0628Z held the LOCK, task: promotion of rows β = −0.02, −0.01); it released the LOCK at 08:30Z (5c06d2e); LOCK taken 08:47Z. Work picked disjoint from that run's rows.

**THE RESULT:** part 1 (statement fidelity, T2b hypothesis necessity): the two open hypotheses of the van der Waals coexistence claim (`b > 0`, `b < v_l`) — scratch Lean in `lean/`.

## Next run's starting point (kept current)
- 08:45Z: scratch `lean/VdWMaxwellRight.lean` being written (every Maxwell coexistence state of the vdW isotherm with c, b > 0 lies right of b; for b ≤ 0 none with v_l > b). If this run vanished: compile it with `lake env lean`, move to `Checked/Trust/`, add to `Checked.lean`, drop `Chemistry.Coexistence.vdW_coexistence_unique | 3, 4` from `scripts/trust/necessity_open_baseline.txt`, rerun StatementDeps.
