# Run 2026-11-08T0428Z (scheduled)

**THE RESULT:** in progress — part 2 (rotation: run 0228Z took part 1; STATE exact next step 2: Homann axisymmetric stagnation flow with the Hiemenz tools). Stub; the front page is written at the end of the run.

## Start
- 04:28Z: add_repo not exposed; pre-cloned checkout detached with a stale diverged local main; `git checkout -B main origin/main` = a6d46f5. **LOCK held by run 0228Z (alive, heartbeat 04:26Z)** → work staged in this folder (PROMPT working note "A live LOCK is not idle time"); Work/ is not touched on main until the LOCK is released.
- Local Lean: elan + Mathlib cache ≈ 3 min.
- Freeze (this commit): `lean/Homann.lean` — three statements with `sorry` (undershoot at q(0) = 1.3119376938, overshoot at 1.3119376939, existence of a boundary-value solution with f''(0) between them), compiled locally. Moves byte-identical to `Work/Homann/Homann.lean` once the LOCK is free.
- Float study `scripts/hm_fast.py`: f''(0) = 1.31193769387980…; generator `scripts/gen_homann_w.py` (from the Hiemenz generator with the coefficient 2): 96 cells, h = 1/16, degree 10, both events certified in exact arithmetic on [0, 6] (path margins 5.6e-10 / 3.1e-11, end margins 1.2e-10 / 1.7e-10, final radius 2.3e-13).
