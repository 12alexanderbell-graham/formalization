# Run 2026-11-08T1628Z (scheduled)

**THE RESULT:** parts 2/5 — the Falkner–Skan β = 1/2 row in the class −1 ≤ f' ≤ 1 (window, equality, existence) frozen, audited, proved and promoted to Checked in one run (e62e945), the first half in auditor role.

**What can a scientist now trust without checking it themselves, that they could not before?** That *every* solution of the β = 1/2 Falkner–Skan boundary-value problem with −1 ≤ f' ≤ 1 has f''(0) strictly between 0.927680039 and 0.927680040, that two such solutions are the same function on [0, ∞), and that one exists with 0 ≤ f' < 1 — before, Lean said only that *a* solution has its wall shear there.

**Measure:** Checked headlines 204 → 207, NV 135/135; six bounded-class and two Falkner–Skan headlines PROVED (CI 42491111671 green on every job). **Weakest unchecked step:** whether f' < 1 alone suffices (unproved here; the classical unrestricted uniqueness is read second-hand only).

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
- c6a98c8: Work proofs (statements byte-identical) + blind restatement closed in full (`Work/FalknerSkan/HBBlindClosed.lean`); axioms propext, Classical.choice, Quot.sound.
- e62e945: promotion (`scripts/promote_hb.py`): `Checked/FalknerSkan/HalfBounded.lean`; literal readings from the existing readers (`SecondReadingFalknerSkan`, `SecondReadingBound`), no new numeral; 2 NV witnesses; audits +4; relock (Witnesses module-doc block named in LEDGER), TRUST_MAP, CLAIMS, packet. Local: full `lake build Checked` 16:31–17:48Z, incremental build, StatementDeps (207 headlines, NV 135/135), Claims, every Python trust check incl. `--base c6a98c8` green.

## f' < 1 alone (next step 4): not attempted beyond exploration
Two exact identities along any solution of f''' + k f f'' + 1 − f'² = 0 (p = f', q = f''), checked by hand: E = q²/2 − p³/3 + p has E' = −k f q²; J = q + k f (p − 1) has J' = (p − 1)((1 + k) p + 1). Neither gives a sign argument by itself (f changes sign along a dipping trajectory). Recorded in STATE item 4 for a later run.

## CI
- 9062ed7 (42491111671, run 1428Z's brief commit; its tree contains 2785b03): **green on every job** (checked: Lean 23 min, trust step 5 min, frozen registry, author files; work; nanoda shards memoised) → the six bounded-class headlines of run 1228Z and the two Falkner–Skan rows of run 0828Z are PROVED.
- This run's pushes (868336e 42501629369, c6a98c8, e62e945, records): read next run.
