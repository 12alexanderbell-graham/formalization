# T5 round T, judged (run 2026-11-07T1828Z)

Red team T: Sonnet, blind, brief `briefT.md` (committed in 722f1c0 before it started), read-only snapshot 4986002 (main with every rule of run 1428Z: V8 repaired, V9–V11, S2, controls). Defects: `redteamT/d01…d06` (its report: `redteamT/REPORT.md`).

Judge: `judge_T.sh` (= `runs/2026-11-07T1428Z/t5/judge_RS.sh` plus the column's `controls/` and `claim_vocab_baseline.txt`, plus `check_audits.py`) on worktree fzJ = 4986002 + all six defects, after one full `lake build Checked` (18:31–19:41Z). Log: `judgeT.out`. Generated CLAIMS.md sections of the three new headlines: `judgeT_CLAIMS_excerpt.md`. Per-defect attribution by rerunning `check_claim_vocab.py --report` and `check_audits.py` with the AFTER scripts.

Lean side: the three new files compile; build, sorry/axiom grep, StatementDeps with relock (non-vacuity, pins, frozen registry) and Claims PASS. Every defect is VALID.

| defect | surface | BLIND = 4986002 scripts | AFTER = 9091d4a (+ acronym split) scripts (not blind) |
|---|---|---|---|
| d01 FINDINGS F8: the z values of the two certified Milne percentages swapped (0.56 % ↔ 6.7 %) | certified-number context | ACCEPTED | ACCEPTED (open: a record certifies a value, not the argument the prose attaches to it) |
| d02 new headline, byte-identical to `gelfand_pde_radial_exists`, paraphrase "there are two functions u" over `∃ u` | numeral counting a noun | ACCEPTED | caught: D1 (duplicate claim), V14 ('two functions' — the claim's 2 is the order of `ContDiffOn ℝ 2`) |
| d03 new headline = `townes_exists`, paraphrase code span `-(1 / r * φ r) + θ r + θ r ^ 3` (θ³ sign flipped: defocusing, no decaying positive solution) | code span with no relation | ACCEPTED | caught: V12 (formula span not in the claim), D1 |
| d04 STATE Blasius bullet: "the whole velocity profile f'(η) and the displacement thickness are certified to the same fourteen digits" | status prose outside S2's list | ACCEPTED | ACCEPTED (open: S2 is a deny-list; STATE.md is declared unchecked prose by its banner) |
| d05 README bullet + run 2026-10-30T0828Z `audit.md` "Scope: Lean covers every curvature" for the flat-only `BambaY` | method claim in records | ACCEPTED | caught: R1 (`check_audits.py`: a closed run record modified a week later); the README sentence alone is still read by no check |
| d06 new headline `GelfandPDEThreshold.gelfand_pde_radial_solvability_threshold` = the one-sided bound `lam ≤ 3.321992119` | name | ACCEPTED | caught: V13 ('solvability', 'threshold' are not claim or disclosed words), D1 |

**Blind: 6/6 valid defects ACCEPTED** (third consecutive round in which every valid defect, or all but one, passes the newest rules: R 4/5, S 6/6, T 6/6). After this run's rules: 2/6 (not blind).

## Reading
- All six went into reader-facing prose next to a correct kernel term again; the brief allowed two Lean-side defects and the red team used none — the statement side (StatementDeps, readings, witnesses) remains unattacked, so its false-acceptance rate is unmeasured, not zero.
- Three of six were the same move: register a byte-identical copy of a true headline and give it a new name or paraphrase. D1 closes the move itself instead of the three word shapes it carried.
- V12 and V13 are allow-lists (a formula span is a quotation; a name word is a claim word or a disclosed one), replacing the relation-only V11 scope and the STRENGTH deny-list of V8. V14 is a context rule for numerals (an allow-list on the counted word).
- Open after this round: certified numbers bind no argument (d01); STATE.md status prose (d04) and README.md prose are read only by deny-lists or not at all. The structural fix for both is generation: print the record's quantity and arguments from the Lean record next to the certified token, and generate the Results section of STATE.md from CLAIMS.md.
