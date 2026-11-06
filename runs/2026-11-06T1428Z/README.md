# Run 2026-11-06T1428Z (scheduled)

**THE RESULT:** part 5 (mathematics): the Gelfand critical parameter of the 3-D ball promoted to Checked, with its equation read a second time by a blind reader (PROVED once the CI of fb999b2 is green); part 3: blind round O measured (6/6 wrong claims accepted) and five of its six classes closed.

**What can a scientist now trust without checking it themselves, that they could not before?** That the Gelfand statement's equation w'' + (2/s)w' + e^w = 0, its λ = s²e^w and its centre condition w(0) = 0 are the radial Gelfand problem of the 3-D ball as an independent reader derives it from Δu + λe^u = 0 (not only the author's transcription), on top of last run's enclosure λ* ∈ [3.321992118, 3.321992119] — now in Checked, under every trust check. And that a headline's docstring can no longer draw a consequence ("so …"), a headline's name can no longer generalise past its statement, a one-sided bound can no longer be called agreement "to within", and a reader can no longer be handed an answer by a side file: each of these got a wrong claim past every check in round O.

**Measure:** Checked mathematics headlines 2 → 4 (PROVED once CI is green); T5 blind false acceptance round O **6/6** (round N 4/6); after this run's rules 1/6 (not blind).

**Weakest unchecked step:** prose outside headline docstrings and names — Work module docstrings and STATE.md sections (round O d03 still passes: a Work wrapper and STATE claiming the Gelfand PDE side closed). For the Gelfand result itself: the PDE side (radial solutions with s < 41/10, symmetry, λ* = sup of solvable λ) is not formalised; and the CI of the promotion was not yet read (queue).

## Start
- 14:27Z: no LOCK; pre-cloned checkout detached, stale local main diverged; `git reset --hard origin/main` = d8bb29e. add_repo not exposed. Local Lean: elan installer accepted, Mathlib cache fetched.
- CI read: **6f0816d 42213870801 green on every job** (Robertson t = 10¹¹ PROVED); e5766ae, 9d47b80, 81fd7f4, e0d7303 green. Later 1228Z pushes still in the CI queue.

## Work
1. **Bottleneck** (STATE next step 2): the Gelfand result sat in Work. A yes puts the first certified mathematics answer not in print into Checked under every check; a no names the check the mathematics statement shape fails.
2. Cherry-picked the promotion draft (`wip/gelfand-checked`) onto main; full `lake build Checked` started detached (first attempt OOM-killed after 10 min; rerun with MMCerts first, ≈ 60 min).
3. **What the literal check needed:** the statement uses no program definition, so every numeral of the equation (2/s, s², 0, w(0) = 0) needed a second reading. Brief with an exact Lean template and capital placeholders (`brief_gelfand.md`, committed alone), Sonnet reader derived 2, 2, 0, 0 from the PDE in ≈ 30 s (reading committed alone), copy to `Checked/Trust/SecondReadingGelfand.lean`. The domain lengths 41/10 and 1/2 are no source data: new check_literals rule (a5), adversary (Sonnet, ≈ 2 min) found 3 holes in the first version (ray moved by a wrong source end time — recorded limit; intervals compared or measured pin S; other spellings of S), two closed before adoption.
4. **Promotion** fb999b2: headlines registered, NV witnesses (S = 41/10 from the existence theorem; the existence headline at S = 1/2 — the relock first failed on it), relock (176 headlines, NV 115/115), CLAIMS 176, packet; every python check green with --base 301e4f1.
5. **Round O judged** (`t5/RESULTS.md`, `judge_O.sh`, `judge_O.out`): 6/6 accepted before; new rules check_claim_words W1–W5 and check_blind_route B5 (written after the report): 1/6 after (d03).

## Notes
- The three local commits brief → reading → copy were rebased onto the LOCK heartbeat 301e4f1 before the first push (local, unpublished history); the reading's commit message cites the brief's pre-rebase hash (LEDGER).

## End
- Records: STATE (Gelfand section, results, trust track, environment, daily review, exact next step), LEDGER, CHANGELOG, PROMPT working notes (domain lengths; OOM of the full build); LOCK removed. CI of fb999b2 and of this commit: next run.
