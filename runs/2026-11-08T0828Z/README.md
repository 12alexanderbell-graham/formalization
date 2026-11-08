# Run 2026-11-08T0828Z (scheduled)

**THE RESULT:** parts 2 and 1 moved: two rows of the classical Falkner–Skan wall-shear table are now machine-checked — β = 1/2 (a solution with f''(0) ∈ (0.927680039, 0.927680040)) and β = 0 (every solution has f''(0) ∈ [0.4695999883610, 0.4695999883611]) — obtained from the certified Homann and Blasius theorems through a proved similarity scaling, with no new numerical certificate; frozen, proved, audited (blind restatement closed, referee STANDS, blind literal reader) and promoted to Checked in one run. Also an audit correction: the Homann record of run 0428Z called its constant unprinted; it is the β = 1/2 row times √2, printed to 15 digits.

**What can a scientist now trust without checking it themselves, that they could not before?** That the Falkner–Skan problem f''' + ff'' + β(1 − f'²) = 0, f(0) = f'(0) = 0, f' → 1 has, at β = 1/2, a solution whose wall shear lies in (0.927680039, 0.927680040), and that at β = 0 every solution has wall shear in [0.4695999883610, 0.4695999883611] — and that the program's own record of what was "new" about Homann's constant was wrong and is now corrected.

**Measure:** Checked headlines 192 → 194 (NV 126 → 127 witnessed); certified Falkner–Skan table rows 1 (β = 1, Hiemenz) → 3; certificate cost of the two new rows: zero (a ≈ 60-line scaling lemma); freeze → promotion ≈ 80 min, of which the full local build 70 min.

**Weakest unchecked step:** uniqueness of the β = 1/2 boundary-value solution (and of Hiemenz and Homann): reported in print (Coppel 1960; Craven–Peletier 1972) but read only second-hand and not formalised, so `fs_half_exists` places *a* solution in the window. Second: the rounding precisions given to the blind reader were chosen knowing the frozen windows.

## What we did
- Start (08:27Z): LOCK held by run 0628Z (heartbeat 07:11Z, alive) → auditor role on the newest frozen claim (Homann). Found that f''' + 2ff'' + 1 − f'² = 0 is Falkner–Skan β = 1/2 under F(s) = √2 f(s/√2); prior-art search: β = 1/2 is called "Homann flow" in the Falkner–Skan literature (Zhu et al., Fazio) and its wall shear is printed to 6–15 digits. Scaling lemma and both corollaries compiled in `lean/` (`FSScale.lean`, `FSRows.lean`) against the built Checked modules.
- 0628Z released the LOCK (6da944f); LOCK + README stub a101965. Freeze c7ff08d; re-freeze fee90fc before any proof (the first windows were images of the Homann/Blasius windows, which no rounding rule reproduces).
- One wave (Sonnet): blind literal reader (brief 1fad98b → reading, committed fdf09cd), blind restater (`blind/`), referee (`referee_fs.md`: STANDS; arXiv:1907.09912 prints 0.927680039836653 and 0.469599988361).
- Work proofs + blind closure 0a532a1 (`Work/FalknerSkan/`). Promotion by `scripts/promote_fs.py`; NV witness from the rescaled Blasius solution; registrations; full local build, StatementDeps with relock, Claims, every Python trust check.
- Records: STATE (new section, Homann correction, Results, environment, daily review, exact next step), LEDGER (promotion; Homann audit correction), CHANGELOG, BLUEPRINT, PROMPT working note (map a new equation into its family before calling a constant new).

## CI
- 129f217 (42453268112, Homann promotion): green on every job (read by run 0628Z).
- fdf09cd (42464403738): work job red in the elan install step (GitHub returned 504 for the elan download) — infrastructure, not the tree; later runs re-judge the same Work tree.
- 0a532a1 (42464635792, Work proofs) and the promotion/records commits: see below or next run.
