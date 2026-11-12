# Run 2026-11-12T1828Z (scheduled)

**THE RESULT:** parts 2/5 by rotation — the reverse-flow (second) Falkner–Skan branch certified at four decelerating rows (β = −0.15, −0.17, −0.18, −0.19: ten-decimal wall-shear windows, existence, two decay-class solutions per row), PROVED in Work + AUDITED (referee STANDS, blind restatement instantiated and closed); rows −0.17, −0.18, −0.19 promoted to Checked (`Checked/FalknerSkan/NegReversedRows.lean`). Part 1 from the same certificates: q > 0 NEEDED in the three attached-row windows.

**What can a scientist now trust without checking it themselves, that they could not before?** The reverse-flow skin friction f''(0) of the Falkner–Skan boundary layer at β = −0.15, −0.17, −0.18, −0.19 to ten decimals (−0.1334212379 … −0.0713359060), with existence and |f'| ≤ 1 — Ganapol's 2010 reverse-flow table is now machine-confirmed at these rows to all twelve printed digits — and that the attached-row claims at −0.17 … −0.19 really need their positive-shear assumption (a certified second solution meets every other assumption).

**Weakest unchecked step:** the restatement audit of the new rows is run 1228Z's blind restatement instantiated per row by script (not a new blind restater); uniqueness of the reverse-flow branch in its class is numerical only (referee scan); the promotion's β readings are run 1428Z's blind readings of the same β in Ganapol's attached Table 6; row −0.15 stays in Work.

## Start
- 18:28Z. add_repo not exposed; pre-cloned checkout detached with a stale local main (54/72 diverged, its commits are on `origin/wip/*`; kept as local branch `stale-local-main-backup-1828`); `git checkout -B main origin/main` = 6a660ac. No LOCK → LOCK taken (7ef5a78).
- Local Lean: elan + Mathlib cache (≈ 3 min); CI artifact `checked-build` of 43268238201 (6a660ac) restored in 51 s.

## CI read
- 43268238201 (6a660ac, run 1628Z's final push, the first main run with `defaultTargets = ["Checked"]`): **green on every job** — checked (strict) 64 min, nanoda 4/4, work 108 min. Run 1628Z's repair confirmed (no 240-min timeout). → `NegWallShearRows` (1428Z) and records F12–F14 (1028Z) PROVED; L.2 message sent (F12–F14 verified, Bonnor–Ebert PROVED, this run's rows).

## Bottleneck (and what a yes/no changes)
- Parts 2/5 by rotation; STATE next step named reverse-flow chains at the Ganapol rows, which also close q > 0 there (part 1). Yes: a certified reverse-flow table segment and three hypotheses classified with one set of certificates. No: record which chain fails.

## Work
1. Float shooting (`scripts/shoot_rev.py`, DOP853): reverse-branch boundary at K = 20/3, 100/17, 50/9, 100/19 (and 2500/497 as control: agrees with run 1228Z's referee to 1e-13). `scripts/plan_rev.py` → `rows_rev.json` (ten-decimal windows, shooting values halfway to each window end, tube ball).
2. Chains (`scripts/make_chains.sh`, run 1228Z's `gen_rev.py`): over at L = 5 (17/4 failed for −0.17: p − 1 not yet positive), slowL at L = 17/4 (−0.15, −0.17) and 5 (−0.18, −0.19: end condition failed at 17/4 by 2e-11 / 5e-11), tube on [0, 3/2]; all OK in ≈ 3 s each. Cells in `cells/`.
3. `scripts/emit_rows.py`: twelve modules `Checked/FSRev/R{Fifteen,Seventeen,Eighteen,Nineteen}{Over,Slow,Tube}.lean` (helpers); all compiled first time (36–226 s each).
4. Freeze 33cd0de (`Work/FalknerSkan/ReversedRows.lean`, `scripts/make_rev_rows.py freeze`): the statements of the audited β = −0.1988 reversed pair with β and window replaced. Proofs cab49ad (`make_rev_rows.py prove`; one fix: the window bullets' sign forms, by `ring` + `linarith`); statements unchanged (script diff); axioms standard (`lean/axioms.log`).
5. Referee (Opus, ≈ 11 min, `referee/REPORT.md`): **STANDS** — own Taylor integrator at 30–60 digits, values agree to 19–22 digits across L = 12–16 and two far-field conditions: −0.13342123789528869657, −0.11422723909825489649, −0.09769206013457255615, −0.07133590600343803100; narrowest margin 1.75e-12 (−0.17); exactly two fast-approach solutions per row in a scan; truncation at L = 10 would be off by 2e-10 (outside the −0.15 window). Printed: Ganapol 2010 Table 7 p. 23 (typeset crop) all four correct to 12 digits; Fazio 2012 Table 4 p. 30 (−0.15, −0.18) correct to 6; **Stewartson 1954 as quoted by Fazio (−0.132, −0.097) wrong in the third digit** (secondary quote, original not checked; parked: changes no conclusion of this program).
6. Blind closure: `scripts/make_rev_closures.py` → `Work/FalknerSkan/ReversedRowsBlindClosed.lean` (run 1228Z's restater's text per row, printed-value theorem dropped).
7. Part 1: `Checked/Trust/NecessityS.lean` (`rev_witness`): q > 0 NEEDED in `fs_neg_wall_shear_17/18/19_window`; compiled first time. Relock: needed 483 → 486, open 307 → 304.
8. Promotion (`scripts/promote_rev_rows.py`): `Checked/FalknerSkan/NegReversedRows.lean` (six headlines, no hypotheses), headlines and literal readings registered (run 1428Z's blind β readings of the same rows).
9. Records (annex LIV): STATE.md had passed 300 KB; older environment lines, older "Last updated" summaries and run 1628Z's long next-step item moved verbatim to `_archive/STATE_environment_history.md` (PROMPT note).

## Local checks and push
- See the final commit message; `local_frozen_step.py --trust 6a660ac` is the replica.

## Next start
- CI read first: this run's final push (NegReversedRows promotion + NecessityS + twelve certificate modules). Green on every job → six `NegReversedRows` headlines PROVED.
- Next by rotation: part 3 or 1; or the rest of Ganapol Table 7 (β = −0.01 … −0.16, all K ≥ 5; float shooting of −0.11 … −0.16 already matches Table 7 to 12 digits) by the same scripts; row −0.15 promotion (blind β reading of Table 7).
