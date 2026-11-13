# Run 2026-11-13T1640Z (scheduled)

**THE RESULT:** parts 2/5 by rotation (parts 2/5 last moved at run 0628Z; four runs since without progress) — the four attached Falkner–Skan rows β = −0.13, −0.14, −0.15, −0.16 certified to ten decimals with existence and promoted to Checked, so every row of the decelerating segment of Ganapol 2010 Table 6 (β = −0.13 … −0.19) is a Checked statement (pending CI).

**What can a scientist now trust without checking it themselves, that they could not before?** The Falkner–Skan wall shear f''(0) of the attached boundary layer at β = −0.13, −0.14, −0.15, −0.16, to ten decimals, for every solution of the physical class (positive shear, approach to the outer stream faster than every exponential), with existence — β read blind from the typeset table, the statement template blind-restated earlier and refereed again; together with rows −0.17 … −0.19 the whole decelerating segment of Ganapol's Table 6 (seven rows) is machine-checked, and each printed 12-digit value lies in its certified window.

**Weakest unchecked step:** the restatement audit of the new rows is the run-1028Z blind restatement instantiated per row by script (not a new blind restater); hypotheses 4, 5, 8 of each new window are open (disclosed in LEDGER); CI has not yet judged the promotion. The values confirm a published table (prior art: Ganapol 2010, Katagiri 1985): a certification of known numbers, not a new number.

## Start
- 16:40Z. add_repo not exposed; pre-cloned checkout detached with a stale local main (its three extra commits are on remote `wip/` branches); `git fetch --unshallow` + `git checkout -B main origin/main` = ad2a969. No LOCK → taken (722914c).
- CI at start: 43462297471 (c5c2a35, run 1522Z's push) in progress (checked job building since 16:26Z; nanoda shards running).
- Local Lean: elan installer accepted; `lake exe cache get` ≈ 4 min; CI artifact `checked-build` of 43422957898 (028d5c4) downloaded ≈ 1 min, restored 41 s (needed `pip install zstandard`); incremental `lake build Checked` for main: seconds.

## Bottleneck (and what a yes/no changes)
- Parts 2/5 by rotation. STATE item "Parts 2/5 next" of run 1428Z: promote row −0.15, more attached rows. Ganapol Table 6's decelerating segment had three Checked rows of seven. Yes: the segment is a set of Checked statements (the second complete printed table after Table 7). No: record which row's certificate fails.

## What we did
1. Blind β reading (Sonnet; brief 18f97ce alone, reading 07defa6): rows 1, 2, 4 of the crop of Table 6 → −13/100, −14/100, −16/100; the reader derived the equation (sympy) and flagged that the full printed Table 6 starts at β = 1.00 (the brief counted rows in the crop, the decelerating segment; the Checked copy's module doc says so).
2. Float shooting (`scripts/rows.py`, copy of run 1428Z's) and the exact generator `runs/2026-11-11T0828Z/scripts/gen_neg_wc_theta.py` (FS_THETA = 11/15, h = 1/32, degree 12, 10⁻¹⁸): all six chains OK in seconds (end margins 3.5·10⁻¹² … 7.1·10⁻¹¹).
3. Freeze 67f8eef (`Work/FalknerSkan/AttachedRowsTop.lean`, `scripts/make_rows.py`). Referee (Opus, ≈ 12 min): **STANDS** — mpmath 40 digits and solve_bvp with the parabolic-cylinder far-field condition; margins ≥ 1.18·10⁻¹¹; Ganapol Table 6 correctly rounded on the three rows; `hdec` essential (a continuum of algebraically decaying attached solutions otherwise); prior art Ganapol/Katagiri (`referee/REPORT.md`; the harness refused the referee's own write, the main session copied its hand-back).
4. PROVED in Work (f62e1b2): six certificate modules (≈ 100 s each), cores, statements unchanged; axioms standard (`scripts/axioms.log`); blind-restatement closure per row (`Work/FalknerSkan/AttachedRowsTopBlindClosed.lean`, `scripts/make_closures.py`).
5. Promotion (`scripts/promote_rows.py`, f29a4fe): rows −0.13, −0.14, −0.15, −0.16 → `Checked/FalknerSkan/NegWallShearRowsTop.lean` (eight headlines), `Checked/FSAtt/R…`, reading copies, NV witnesses, literal readings; `Checked/Trust/NecessityX.lean`: hypotheses 1, 2, 3 NEEDED and 6 REDUNDANT in the four windows by the coefficient-generic lemmas of NecessityQ/NecessityR, and 7 (0 < q) NEEDED by the reversed-flow headline of the same row (Table 7): 20 classifications. Local `lake build Checked` green.

## Local checks and push
- Local: `lake build Checked` green (incremental on the restored CI build of 028d5c4; 12 FSAtt certificate modules ≈ 2 min each). StatementDeps with relock: 279 headlines, NV 168/168, necessity needed 530, redundant 153, open 279 (was 267 at start: + 3 open per new window). Claims, packet.
- CI replica `local_frozen_step.py --trust 028d5c4`: first run red at check_necessity N1 (new windows' open hypotheses need lines in `necessity_open_baseline.txt`); while repairing, hypothesis 2 was classified as well (NecessityR's integrating-factor profile); second run: **trust step exit 0, frozen step 21 commands, 0 failed**.
- Intermediate pushes carried `[skip ci]`; the final push (LOCK removed) starts the main run that judges the promotion. CI of c5c2a35 (43462297471) still running at 18:25Z (checked job building since 16:26Z; nanoda shard 0 green).
- Lessons (PROMPT note): name table rows by a property visible on the whole page; the reversed-flow headline at the same β is the `0 < q` necessity witness; referee reports may have to come back as text. A new window headline needs both a LEDGER `open` line (N2) and a `necessity_open_baseline.txt` line (N1).

## Next start
- CI read first: 43462297471 (c5c2a35) and the run of this run's final push. Green on every job → the eight `NegWallShearRowsTop` headlines PROVED; one L.2 line to Alexander (Ganapol 2010: Table 7 19/19 and Table 6's decelerating segment 7/7 Checked).
- Then by rotation part 3 (STATE 0f) or part 1 (hypotheses 4, 5, 8 of the attached-row windows). Parts 2/5 later: Ganapol Table 5's near-separation rows (generator end condition, 12–13-decimal windows).
