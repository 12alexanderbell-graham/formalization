# Run 2026-11-09T1828Z (scheduled)

**THE RESULT:** part 3 (rotation: part 3 at 1428Z, parts 2/5 at 1628Z) — **the content of a blind reading is now checked by Lean**: every SIGN or CLAUSE reader line that a generated claim shows about a pinned definition is either proved about that definition by a Checked theorem (`Checked/Trust/PhraseCerts.lean`, registry `scripts/trust/phrase_certs.txt`, rule P13) or listed in a shrink-only baseline, and the theorem's conditions are printed after the phrase in every generated claim. A new reader line can no longer reach CLAIMS.md on a model's word. Certifying found **five shown lines false at edge values** (Ω0 "positive curvature constant gives above one", redshift "zero when emission and observation coincide", cosmographic coefficients "orders 0 and 1 are one", curvK sign, Duffing "v₀ the initial velocity").

**What can a scientist now trust without checking it themselves, that they could not before?** That the explanatory sentence attached to a defined quantity in a generated claim (e.g. "Ω0 … positive curvature constant gives above one") is a theorem about the Lean definition, with the exact conditions under which it holds printed next to it ("only assuming `0 < K`; `hubble a t₀ ≠ 0`; `a t₀ ≠ 0`") and its full statement in PHRASE_LINES.md — not a reader's paraphrase that may fail at values the formulas allow.

**Measure:** reader lines of phrases proved in Lean 0 → 31 of 92 (SIGN 5/13, CLAUSE 26/79); lines found false as shown and now printed with their conditions: 5; adversary AE on P13 as first implemented 6/6 defect classes passed, after repair 2 open (`adversary/JUDGE.md`).

**Weakest unchecked step:** whether a certificate's statement says what its line says is still judged by the author (AE d02 residual: the docstring must quote the line and the definition must be in the conclusion, but a weaker statement passes; a reader sees it only in PHRASE_LINES.md). 61 shown lines remain uncertified (baseline: 34 owed, 27 names/roles/units/conventions).

## Start
- 18:28Z. add_repo not exposed; pre-cloned checkout detached at 739510a with a stale diverged local main; `git checkout -B main origin/main` = 739510a. No LOCK; taken 254d087.
- Environment: repo reachable (push). **Local Lean available**: the official elan installer ran this time (run 1628Z's environment had refused it); `lake exe cache get` ≈ 3 min; full `lake build Checked` 18:38–19:56Z (78 min; PhraseCerts' imports built first), incremental pass for PhraseCerts 1 min; StatementDeps with relock and Claims ≈ 8 min each.
- CI at start: c143ec5 (42672836422) and 739510a (42672998445) "failure" = checked job cancelled by coalescing (goal guard, packet, changes green); 254d087 (42674337617) completed in 51 s with no job (GitHub side); c7e1ad9 (42662510643) work green, nanoda 4/4 running. So the β = −1/10 promotion has had no checked job on main yet.

## Bottleneck
STATE exact next step 3(a)/(b): the content of a blind reading (adversary AD d02/d04: a new honest-looking reading restating an excluded overclaim reaches CLAIMS.md on one model's word) and the known-false `omega0` SIGN line that no route could take out. A yes: lines are theorems, so false ones cannot be certified and new ones need a proof; a no: the lines are too informal to state in Lean (then a second blind judge, item 3(a) as planned).

## Work
1. `Checked/Trust/PhraseCerts.lean`: one theorem per property a reader line states, conditions as hypotheses; `*_needs_*` theorems show the conditions of the Ω0, redshift and cosmographic-coefficient lines cannot be dropped (Mathlib's x/0 = 0).
2. `scripts/trust/phrase_certs.txt` (34 CERT lines, 31 reader lines), `phrase_cert_baseline.txt` (61 lines: 34 in group A, owed; 27 in group B, no property), `check_claims.py` P13 + planted controls, `Claims.lean` (certificate checks, conditions after phrases, PHRASE_LINES.md), CI staleness check and author-files tarball.
3. Adversary AE (Sonnet, brief committed in e74041e's parent tree as `adversary/BRIEF.md`, run on snapshot 86c07c9): 6 defect classes; repairs before the first push (`adversary/JUDGE.md`).
4. Branch `wip/p13` (e74041e) pushed for a CI build and author files in parallel with the local build.

## Local checks
Full `lake build Checked` green (incl. PhraseCerts; every PhraseCerts theorem on propext/Classical.choice/Quot.sound only); StatementDeps with relock (232 headlines, NV 154/154, necessity 161/17/665: unchanged); Claims.lean (232 claims, PHRASE_LINES.md, 0 generator errors after allowing predicate certificates to use the predicate in a hypothesis); every Python trust check and every `--base 8c80eb9` check green; P13 planted controls green; `make_packet --check`; goal guard; check_status_lines.

## CI
- `wip/p13` (42681133363, e74041e): goal guard red (run README stub had no THE RESULT line yet; fixed), checked job running at 20:05Z; a parallel build only.
- Main push of this run (P13 + records): read next run (STATE exact next step 1).

## Lessons
- Writing a reader's sentence as a Lean statement is the fastest falsifier the program has: five false lines in under an hour, each of which had passed three blind readers and the main session.
- Python's `str.strip()` and Lean's `trimAscii` disagree on Unicode white space: any registry read by both must ban non-ASCII separators (AE d01).
