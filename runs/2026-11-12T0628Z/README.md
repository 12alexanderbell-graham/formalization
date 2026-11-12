# Run 2026-11-12T0628Z (scheduled)

**THE RESULT:** parts 2/5 and 1 — **the Bonnor–Ebert critical sphere is in `Checked`** (run 0427Z's promotion branch finished: a new blind literal reading whose template carries its imports, so the copy keeps the reader's code) **with every hypothesis of the claim classified** by machine-checked witnesses, and **nine hypotheses classified by symmetries of the equations** (`Checked/Trust/NecessityM.lean`: the isothermal scaling u(s) = w(cs) + 2 log c makes the centre value w(0) = 0 NEEDED for Bonnor–Ebert and the Gelfand ball; Thomas–Fermi 1; Gelfand PDE 2, 3). NEEDED 422, REDUNDANT 118, open 349, fully classified 56 of 155. PROVED once the main run is green on every job.

**What a scientist can now trust without checking:** that the Bonnor–Ebert statement (critical radius, mass coefficient, density contrast) assumes nothing decorative — each of its five assumptions is shown in Lean to be needed (the claim fails without it) or redundant.

**Weakest unchecked step:** the claim certifies the mass up to radius 7 only (the maximum over all radii needs a tail argument); C-BE-1 (Galli et al. 2002 print 13.98) is not yet decided as finding vs parked misprint; PROVED waits on CI.

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

## Promotion finished (07:33Z–)
- Branch `wip/be-promo-0628` = run 0427Z's `wip/be-promo` (f5194d0) with main merged in (no rebase). Remaining failures of STATE 0e: (1) provenance rule 4 — new blind reading `be_reader/` (brief alone, reading, copy: three ordered commits; Sonnet reader: A=2, B=2, C=4, D=(−1), E=7, all agree). The first copy kept the module path `SecondReadingBE.lean` and failed rule 4 / B1 (they order the reading before the *first* commit touching the module since the base, and run 0427Z's copy was earlier): copied instead as the new module `SecondReadingBE3.lean`, run 0427Z's two copies archived. (2) check_formulas and (3) check_relock — LEDGER line names the reading constants with their brief and `moduledoc:Checked.Trust.Witnesses`. (4) N1 — no open hypothesis left (NecessityM).
- check_prose flagged three numbers in the NecessityM module doc (6.45, 1/3, 3/2): rewritten without them.
- Local: `lake build Checked` green; relock; Claims; packet; `local_frozen_step.py --trust 89aca37` trust step exit 0 (frozen step then failed only at rule 4/B1, fixed by the new module), `local_frozen_step.py cc6673d` 20/20 green after the rename; goal guard, precheck_citations, packet check green.

## Next run's starting point
- Read CI of this run's merge push on main (the checked job ≈ 60–100 min): green on every job → `bonnor_ebert_critical` PROVED; tell Alexander only with a decided C-BE-1 or other L.2 item. Red → `local_frozen_step.py --trust <base>` on the restored artifact.
- Then STATE 0a (move C-FS-SEP, C-FS-1988, C-FS-1988R to verified findings with certified-number tags) and C-BE-1.
