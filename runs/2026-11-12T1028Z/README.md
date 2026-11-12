# Run 2026-11-12T1028Z (scheduled)

**THE RESULT:** parts 2/5 by rotation — the three Falkner–Skan candidates whose Lean evidence is PROVED (C-FS-SEP, C-FS-1988, C-FS-1988R; STATE next step 0a, deferred by three runs) moved to verified findings with certified records.

## Start
- 10:28Z. add_repo not exposed; pre-cloned checkout detached; `git fetch --unshallow` + `git checkout -B main origin/main` = 0e262e6; no LOCK.
- Local Lean: elan installer accepted, Mathlib cache fetched; CI artifact `checked-build` (run 43155541876, 7ddd986) downloaded for restore.
- CI: run 43196172253 of 0e262e6 (carries the Bonnor–Ebert promotion and the AH repair) pending at 10:30Z.

## Bottleneck
- STATE 0a: C-FS-SEP, C-FS-1988, C-FS-1988R have Lean evidence PROVED since run 0227Z's CI read (37b67ea green on every job) but stay "candidates": their decimals are in author prose with no certified record. Yes (records + findings green) → three published-value refutations become verified findings a reader can check number by number; no → the record pipeline cannot carry quantified ODE solutions and needs repair.
