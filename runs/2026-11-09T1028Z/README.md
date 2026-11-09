# Run 2026-11-09T1028Z (scheduled)

**THE RESULT:** parts 2 and 5 — Falkner–Skan with **adverse pressure gradient (β < 0) promoted to Checked**: four headlines (uniqueness and largest wall shear in the class f'' > 0 + faster-than-every-exponential approach, for every β < 0; at β = −1/10 existence in that class, and two solutions with different wall shear outside it). Headlines 224 → 228, NV 150 → 152, hypothesis necessity: needed 155 → 158 (the decay hypothesis of both uniqueness theorems is machine-shown NEEDED). PROVED once a main run is green on every job.

**What can a scientist now trust without checking it themselves, that they could not before?** That the classical β < 0 Falkner–Skan picture (Iglisch & Kemnitz 1955, Hartman 1964: one exponentially approaching solution, a family of algebraic ones) holds in machine-checked form at β = −1/10, with every literal of the four statements read by a blind reader, and that dropping the decay condition provably breaks uniqueness (necessity witnesses in `Checked/Trust/Necessity.lean`, counted in TRUST_MAP.md).

**Measure:** headlines +4 (228), NV 152/152, needed hypotheses +3 (158), blind literal readings +3 constants (`fsnWedgeRhs`, `fsnDefectBelow`, `fsnWallValue`), blind restatements 4/4 closed (one new this run), axioms standard.

**Weakest unchecked step:** whether CI judges the promotion green (checked job, nanoda shards on the new modules); and the prior-art reading rests on a secondary summary (Veldman & van de Vooren 1980) — Hartman Ch. XIV not read.

## Start
- 10:27Z. add_repo not exposed; pre-cloned checkout detached with a stale diverged local main; `git checkout -B main origin/main` = 92c7b40. No LOCK; taken fa2194d (10:31Z), heartbeat 194f097 (12:06Z).
- Environment: repo reachable (push); local Lean: elan + toolchain v4.35.0 + Mathlib cache ≈ 3 min; full `lake build Checked` 10:30–12:05Z (95 min; the promoted modules were added mid-build, so one incremental pass followed, ≈ 3 min).
- CI: 92c7b40 (42593702186): work job green (builds every `Work.FSNeg.*`, `Work.FalknerSkan.Neg*`, `NDBlindClosed`, `NTBlindClosed`), checked job running when read (10:28Z); this run's pushes: next run.

## Bottleneck
STATE exact next step 2: the β < 0 theorems were PROVED in Work only. A yes (promotion through every trust check) puts them in Checked; a no would show a literal or a phrase that no blind route can carry.

## Work
1. Blind literal reading (brief 600017e → reading 0c8270b): m = −1/21 gives β = −1/10, edge value 1, and the decay-class condition with the reader's own edge asymptotics (algebraic approach fails it, Gaussian satisfies it; shooting: continuum below s ≈ 0.317, critical s* ≈ 0.31927).
2. The constant `3` of `fs_neg_tenth_not_unique` is the author's choice, not source data: new literal-free headline frozen d6dc129 (each of the two solutions fails the decay condition itself), proved 2fd45eb from the old one; blind restatement from words (Sonnet, derivWithin + ContDiffOn 3) closed in `Work/FalknerSkan/NOBlindClosed.lean` (516b7c8). Renamed `fs_neg_tenth_outside_decay` before registration (V8: `unique`).
   Docstrings: three rounds against check_claim_vocab/check_prose (V1 words, V11 code must be the claim's own, rule on "each of which").
3. Promotion by script (`scripts/promote_fsneg.py`: 12 `Checked/FSNeg/*` + 7 `Checked/FalknerSkan/Neg*` modules), reader copies `SecondReadingFSNeg`, `SecondReadingFSWall` (second blind reading eef88ef → 8eb3ece after check_literals flagged the `0` of `q 0`), NV witnesses (2), necessity witnesses (3), docstrings rewritten for the claim vocabulary (`scripts/fix_docs.py`), prose_vocab `neg`, `decay`, `max`, `outside` (LEDGER).
4. Promotion commit 83ebad4 (rebased over run 1228Z's auditor-role scratch commits): local full build, StatementDeps with relock, Claims, every Python trust check incl. `--base 92c7b40`, packet, goal guard green.
5. Prior-art screen (`screen/REPORT.md`): substance classical for β* < β < 0; the largest-wall-shear form and machine-checked versions not found.

## Concurrency
- Run 1228Z started 12:27Z in auditor role under this LOCK and compiled the ten-decimal window and the reversed-flow branch in its own folder; this run rebased its promotion commit over those scratch commits (no file overlap) and released the LOCK in the records commit.

## Lessons
- A constant chosen by the author inside an existential conclusion (here `q < 3(1 − p)`) cannot be read blind; state the property it stands for (here: not in the decay class) and keep the constant in a helper.
- A bare wall value `q 0` in a conclusion needs its own reading (`fsnWallValue`); add it to the reader brief whenever a statement compares wall values.
