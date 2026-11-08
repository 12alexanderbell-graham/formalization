# Run 2026-11-08T1628Z (scheduled)

**THE RESULT:** parts 2/5 (exact next step 2 of run 1228Z: the Falkner–Skan β = 1/2 row in the class −1 ≤ f' ≤ 1, window and uniqueness by the proved scaling) and the open widening to f' < 1 alone (next step 4); in progress — auditor role while run 1428Z holds the LOCK.

## Start
- 16:27Z. add_repo not exposed; pre-cloned checkout detached; `git checkout -B main origin/main` = de88fae.
- LOCK: run 2026-11-08T1428Z, taken 14:58Z, heartbeat 15:44Z (alive, < 150 min) → rule 48.4: auditor role; this run writes only in this folder (plus a CHANGELOG append) until the LOCK is released.
- Environment: repo reachable (push); local Lean: elan 4.2.4 + toolchain v4.35.0 + Mathlib cache ≈ 4 min; full `lake build Checked` started detached 16:33Z (2 cores) in the build tree; commits from a second worktree `../fzmain` (working note 146).

## Auditor role (16:27–16:55Z)
- Freeze candidate `lean/FSHalfBounded_frozen.lean` (899bb6c): `fs_half_bounded_window`, `fs_half_bounded_equal` (statements of run 1228Z's compiled scratch) and `fs_half_exists_bounded` (added: the existence member of the trio, 0 ≤ f' < 1, by the inverse scaling of `homann_exists_bounded`).
- Blind restatement (Sonnet, claims in words only, `blind/`) and referee (`referee_fshalf.md`) in one message (988e7b1). Referee **STANDS-WITH-CORRECTIONS**, prose only: P1 the module doc named only c = 1/√2 (existence uses c = √2; fixed before the Work freeze), P2 novelty (uniqueness at β = 1/2 is published, unrestricted, second-hand: Coppel 1960, Craven–Peletier 1972 via Veldman–van de Vooren 1980 and arXiv 2011.07725; the value is printed to 15 digits, 0.927680039836653, Belden et al. arXiv 1907.09912), P3 `Checked/FalknerSkan/FalknerSkan.lean`'s module doc "uniqueness of the half-β solution is not formalised" stays true of that module (frozen; not changed), P4 name the normalisation f''' + f f'' + β(1 − f'²) = 0 wherever the number is quoted.
- Run 1428Z released the LOCK in 334af75 (no Checked/Work change since de88fae, so the running build stays valid).

## Freeze → proof → promotion
- LOCK taken; freeze `Work/FalknerSkan/HalfBounded.lean` (statements byte-identical to the candidate, namespace `Work.FalknerSkan.HalfBounded`; all `sorry`).
