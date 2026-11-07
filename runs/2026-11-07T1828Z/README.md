# Run 2026-11-07T1828Z (scheduled)

**THE RESULT:** part 3 (measured trust) moved: blind round T measured the post-S rules at **6/6 wrong claims accepted**; five rules written from it (not blind) reject 4/6. Auditor role until 18:46Z (run 1628Z held the LOCK); LOCK holder after.

**What can a scientist now trust without checking it themselves, that they could not before?** That a headline's name, every formula written as code in its paraphrase and every number-plus-noun in it come from the Lean statement (or from a disclosed word list), that no headline is a renamed copy of another, and that a past run's audit record has not been rewritten — each enforced in CI with a control. Not yet: the sentences around certified numbers in FINDINGS.md and the status prose of STATE.md; a blind red team still gets wrong claims past the checks every round (6/6 this round).

**Measure:** blind false acceptance, round T: 6/6 valid defects (R 4/5, S 6/6 before). After this run's rules (not blind): 2/6. Prose rules with a control: 10 → 14, plus R1 with its own.

**Weakest unchecked step:** the text next to a certified number (T d01: "6.7 % at z = 1" with both numbers certified and the arguments swapped) — a record certifies a value, not what the prose says it is the value of.

## What we did
- Brief `t5/briefT.md` committed (722f1c0) before red team T (Sonnet, read-only snapshot 4986002 outside the repository) wrote six defects (`t5/redteamT/`).
- One full `lake build Checked` of the snapshot (18:31–19:41Z), all six defects applied, judged with `t5/judge_T.sh` (blind column = snapshot scripts; after column = this run's): `t5/RESULTS.md`, `t5/judgeT.out`.
- Rules (9091d4a + acronym split, not blind): `check_claim_vocab.py` V12 formula spans, V13 name words, V14 counted words, D1 duplicate claims; `check_audits.py` R1 closed run records; controls for each. LEDGER, CHANGELOG, TARGETS part 3, STATE (trust track, environment, daily review, exact next step), PROMPT working note (generate, do not filter).

## CI
- Pushes be039c1 (42402864284), f90b87b (42403744623), heartbeat 32ff7b6 and the records commit: not finished at the close; read next run (STATE exact next step 1).

## Start
- 18:28Z: pre-cloned checkout detached with a stale diverged local main; `git checkout -B main origin/main` (4986002). add_repo not exposed. LOCK held by run 1628Z (taken 16:36Z, heartbeat 18:09Z). Elan installer ran; Mathlib cache fetch started.
- Brief `t5/briefT.md` committed before the red team starts (snapshot 4986002, worktree outside the repository).
- 18:32–18:45Z: red team T (Sonnet, blind, snapshot 4986002) wrote six defects (`t5/redteamT/`). 18:46Z: run 1628Z released the LOCK (0b9051c); this run took it.
