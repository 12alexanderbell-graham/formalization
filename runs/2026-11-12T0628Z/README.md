# Run 2026-11-12T0628Z (scheduled)

**THE RESULT:** parts 2/5 — promotion of the Bonnor–Ebert critical sphere (PROVED in Work + AUDITED by run 0427Z) to `Checked` (in progress).

## Start
- 06:28Z. add_repo not exposed; pre-cloned checkout detached with a stale local main; `git fetch --unshallow` + `git checkout -B main origin/main` = bf7ef60.
- LOCK of run 2026-11-12T0427Z (started 04:27Z, last push 06:17Z, alive) → auditor role (48.4) until its release or 06:57Z.
- Local Lean: elan installer accepted; `lake exe cache get` running. CI build artifact `checked-build` of run 43155541876 (wip/checked-build-artifact, 7ddd986) downloaded (1.9 GB) for the restore trial (LIV experiment of run 0427Z).
- CI: run 43158099652 (89aca37, run 0227Z's records) **green**; run 43160197598 (cc6673d, Bonnor–Ebert in Work) in progress.

## Bottleneck
- STATE next step 0e: promote `bonnor_ebert_critical` to Checked. Yes → a new field (astrophysics) PROVED in the trust system, and C-BE-1 can be decided on Checked evidence; no → a promotion defect (imports, docstring, NV, necessity) to repair.
- Draft promotion script `scripts/promote_be.py` (pattern of promote_g.py) written in auditor role; compile against the restored build.

## Auditor role (06:28Z–LOCK release)
- **Collision (LIV):** run 0427Z's LOCK line said from 06:38Z "promotion of Bonnor–Ebert to Checked in ../fztest"; this run read only the heartbeat times and promoted the same modules in its own tree (local only, never pushed; ≈ 25 min). Root cause and fix: PROMPT working note "Read the LOCK line, not just its time".
- **Disjoint work instead — nine hypotheses classified** (scratch `lean/NecessityM.lean`, compiled against the promoted modules): Bonnor–Ebert 1, 2, 4, 5 needed, 3 redundant (5 by the scaling symmetry u(s) = w(cs) + 2 log c of the isothermal equation); Gelfand ball 5 needed (c = 1/3); Thomas–Fermi 1 needed (explicit pair); Gelfand PDE bound 2, 3 needed (constant shift). StatementDeps on wip/be-promo + NecessityM: needed +8, redundant +1, open −9.
- **CI artifact restore measured (LIV experiment of run 0427Z):** download of `checked-build` (1.9 GB) ≈ 1 min, `restore_checked_build.sh` 68 s, `lake build Checked.Math.BonnorEbert` on top 4.6 min (the six new modules); a later branch build 5.9 min.

## LOCK
- Run 0427Z released the LOCK (f789e4d); taken by this run.
