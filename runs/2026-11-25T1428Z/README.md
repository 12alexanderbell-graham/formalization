# Run 2026-11-25T1428Z

**THE RESULT:** part 3 by rotation (STATE 3g; next step STATE 3h). The round, its judge and its readers are in section What we did; the new rule in the same section.

**What can a scientist now trust without checking it themselves, that they could not before?** That a statement of the claims page shown with no open fidelity objection has none filed under a statement of the same short name instead: a fourth blind red team filed a note that doubts one statement under its namesake, the doubted statement showed "none", and the new rule O3 catches it.

**Weakest unchecked step:** what an objection entry means: an entry is shown open with its text unprinted, and 4 of 4 blind readers declined to cite on it even when its own note withdraws the query (d04, not closed); and, as in round AX, the readers' honesty (a forged brief and reading still passes).

## Start
- 14:28Z. `scripts/start_run.sh`: local main = origin/main bbc1caf; no LOCK; LOCK taken (4bbb761).
- Env: repo ok (add_repo not exposed; the session clone was present). Local Lean v4.35.0 (elan), Mathlib cache; judge's build of 8cc4f5e (artifact of 45608767251) restored by streaming; `lake build Checked` built the five new modules of run 1228Z (3802 jobs); StatementDeps without relock and Claims.lean (outputs and pages unchanged). Disk: about 2 GB free after the restore. Subagents: one red team, four readers (Sonnet).

## CI read
- 45626806307 (21bff96, run 1228Z's final push): green on every job (goal guard, packet, changes, work, checked incl. the trust and frozen steps, leanchecker 4/4, nanoda 4/4). Necessity theorems only: nothing to promote.

## Bottleneck (and what a yes/no changes)
- Round AX's defects passed every check and misled no reader; the fields no round had touched were `literal_slots.txt`, `headlines.txt`, the B3 header exemption and the Status line itself. Does a fourth blind red team, told that readers act on the claim and the head of the Status line, get a record onto the page that changes what a reader would cite? Yes → which field, and a rule. No → the page's record of resisting blind rounds grows by one, and the next round goes to those fields with a larger budget.

## What we did
- **Round AY** (`t5/`): brief `briefAY.md` committed alone (220e359 = snapshot), reader brief `reader_brief_AY.md` committed alone (bd5aec5) before the red team ran; snapshot `/home/claude/fzAY` with this run's StatementDeps and Claims outputs (incl. `phrases.jsonl`, whose absence cost round AX a rerun). Red team (Sonnet, blind, ≈ 32 min) delivered five defects and its untried routes; output committed verbatim (`t5/redteamAY/`) before the verdicts were written.
- **Judge** `t5/judge_ay.sh` (AX's, plus one change: it commits what an apply.py leaves uncommitted, as an author would), two trees in parallel, Claims.lean per defect: verdicts `t5/verdicts_AY.txt`. Two defects accepted by every check, three caught by Claims.lean rule P13. Table `t5/RESULTS_AY.md`.
- **Readers:** two fresh blind Sonnet readers per accepted defect, four in one message, material by round AW's script: **4 of 4 declined to cite** the headline the defect marked as doubted (`t5/READERS_AY.md`).
  - d01: a note doubting `AvilesWitness.printedL0_false_at` entered under `CPLExistence.printedL0_false_at` (O2 asks only that the file name the last name component, which both share): the page shows the namesake as doubted and the doubted statement with "none".
  - d04: an entry on `lookback_second_order_bigO` whose note says the query is withdrawn: shown open (by design since round AV an entry only lowers trust; it leaves only with a re-freeze or a withdrawal of the headline, O1).
- **Fix** (strengthening only): rule O3 of `check_claims.py --base` — an objection whose file names a last name component several listed headlines share must be entered for every one of them (two such pairs today). Controls `_controls_o3`; d01 is caught, the clean tree passes.
- Untried by the red team (section Next): slot swaps in `literal_slots.txt` (it found rule T3 blocks swaps between unequal values), `headlines.txt` (needs a StatementDeps rerun per try), the B3 header exemption (needs a new reader `.lean`), and multi-token reader constants that would cover literals of unrelated headlines if registered (`redteamAY/brute.py`).

## Measure
- Round AY BEFORE: 2/5 accepted by the checks; readers: 4/4 declined to cite on a false doubt (both accepted defects VALID by the pre-registered rule, in the lowers-trust direction; d01 also VALID-BY-HEADER in the raises-trust direction). AFTER: 1/5 accepted (d04, the designed direction).
- Four rounds on the claims page: AV 2/5 valid → closed; AW 5/5 → closed; AX 0/4 valid (4 closed); AY 2/5 valid (1 closed, 1 by design).
- Trust map unchanged (NEEDED 778, REDUNDANT 257, open 31; 312 headlines). No Lean file changed.

## Next
- CI read first: the run of this run's final push (Python check changed: `check_claims.py` O3; no Lean file). Green on every job → nothing to promote. Red → its first failing command with the newest ancestor green on every job (21bff96) as base (`python3 scripts/trust/records_check.py 21bff96`).
- Part 3 next: the false-doubt direction AY measured: an entry whose own note withdraws the query is shown open forever and readers decline to cite on it. Decide, with a held-out reader test, whether an entry may leave the registry through a recorded event other than a re-freeze (for example a blind referee's verdict committed alone under `runs/` and named in the registry, the page then showing "closed by" and that path, never author words), and what that would let a forger do. Then a fifth round on `headlines.txt` with a StatementDeps budget, and the multi-token reader constants of `redteamAY/brute.py`. The Soave record (`source_clause_baseline.txt`) stays as in run 0228Z's Next.
- Part 1 next: as in section Next of `runs/2026-11-25T1228Z/README.md`.
- Parts 2/5 next: as in section Next of `runs/2026-11-25T1028Z/README.md`.

## End
- Local: `scripts/start_run.sh`, judge's build of 8cc4f5e restored by streaming, `lake build Checked` (3802 jobs), StatementDeps (312 headlines, NV 190/190, 778 / 257 / 31), Claims.lean (312 claims), round AY judge (Claims.lean per defect), `check_claims.py --base` with O3, `records_check.py 21bff96`.
- Message to Alexander (L.2): none (no finding, nothing seriously wrong).
