# Run 2026-11-12T0828Z (scheduled)

**THE RESULT:** part 3 (measured trust) by rotation — blind red team AH against the necessity witness layer: full CI caught all 5 valid defects, but the necessity checks alone accepted 4/5 and three were caught only incidentally (statement literals, paraphrase words); repaired: those three now fail N4, and a missing redundancy label (live on main in 7 headlines) is fixed.

**What a scientist can now trust without checking:** that a headline the trust map counts as "every hypothesis classified" does not smuggle an assumption through a proof-carrying data type (`ℝˣ`, `PLift P`, `Fin n`) or a set-membership hypothesis that bundles several conditions, and that redundancy shown hypothesis by hypothesis and part by part is labelled "each alone, not together" whenever two or more are listed (seven headlines were missing the label).

**Weakest unchecked step:** joint redundancy is labelled, never proved; `carriesProof` does not look inside field types (a structure whose field is `ℝˣ`); 349 hypotheses still open.

## Start
- 08:28Z. add_repo not exposed; pre-cloned checkout detached; `git fetch --unshallow` + `git checkout -B main origin/main` = f41efd8.
- LOCK of run 2026-11-12T0628Z (heartbeat 08:03Z, alive; task: Bonnor–Ebert promotion from wip/be-promo, STATE 0e) → auditor role (48.4). Part 3 chosen because 0628Z covers parts 2/5 and part 3 has had no run since 2026-11-11T1628Z (STATE next step 0).
- Local Lean: elan installer accepted, Mathlib cache running; CI build artifact `checked-build` (run 43155541876, 7ddd986) downloading for restore.
- CI: run 43175455329 (f789e4d, run 0427Z's records) in progress; 43160197598 (cc6673d) green.

## Bottleneck
- Part 3: the necessity tally (TRUST_MAP "414 shown NEEDED …, 54/154 fully classified") has had no blind measurement of its *witnesses* (rounds AF, AG attacked the shape layer). Yes (defects caught) → the tally can be quoted as measured; no → each accepted defect names a hole in what NEEDED/REDUNDANT means, to repair.
- Brief `t5/briefAH.md` committed before the round; red team Sonnet, blind, on a read-only snapshot at f41efd8.

## Round AH (08:42Z–09:30Z) — `t5/RESULTS.md`
- Red team returned 6 defects in 11 min (all compiled). Judge tree `../fzJ` = f41efd8 + restored CI build (72 s restore, 1.5 min build).
- BEFORE: `local_frozen_step.py --trust f41efd8` stopped at check_literals (d01–d05: statement literals); every later check run separately: D1 catches d02; d03–d05 meet only vocabulary rules; `check_necessity.py --base` OK with d03–d05 fully classified; d06 caught by the conjunction-hypothesis rule, but its label hole is live on main in 7 headlines. d01 INVALID.
- Repair 6c02253 (`carriesProof`; membership opened in `partsWalk`; label counted across hypotheses and parts). AFTER on the same tree: N4 fails on exactly d03, d04, d05; no existing headline changes shape; tallies on main unchanged (422 / 118 / 349 open; label on 7 lines).

## LOCK
- Run 0628Z released the LOCK (2934d8e, 08:41Z); taken 08:49Z (40cbeca); heartbeat 09:29Z.

## Next run's starting point (written as the run goes)
- If this run vanishes: judge `t5/redteamAH/` (copied verbatim once returned) on main with the restored CI build: apply each defect, `lake build Checked`, `TRUST_RELOCK=1 lake env lean scripts/trust/StatementDeps.lean`, `python3 scripts/trust/check_necessity.py`.
