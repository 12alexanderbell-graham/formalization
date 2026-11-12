# Referee report, run 2026-11-12T2228Z (reversed-flow Falkner–Skan table rows)

Referee: Opus subagent, ≈ 11 min, brief `BRIEF.md` (committed in cf66704 before the referee ran), read only the brief and
`Work/FalknerSkan/ReversedTable.lean`. The subagent could not write files outside its scripts (tool refusal); this
report is its returned text, saved by the run (content unchanged except layout).

## Verdict: all 11 rows STAND

### Task 1: independent high-precision values (`fs_taylor.py`: own mpmath Taylor integrator, dps 40, h = 0.25, N = 26,
secant on p(L; s) − 1, each β bracketed by its own scan of s ∈ [−0.30, −0.01]; L = 8 … 30; at L = 30 repeated with
h = 0.125, N = 32: all 22 digits agree)

| β | referee f''(0) | in window | distance to nearer end |
|---|---|---|---|
| −0.04 | −0.09663678740859116765 | yes | 8.59e−12 |
| −0.05 | −0.10827108328583355116 | yes | 1.42e−11 |
| −0.06 | −0.11792411103838696378 | yes | 3.84e−11 |
| −0.07 | −0.12585853172238540937 | yes | 2.24e−11 |
| −0.08 | −0.13222765437970213420 | yes | 2.03e−11 |
| −0.09 | −0.13711381180237458362 | yes | 2.37e−12 (upper end) |
| −0.11 | −0.14250791030933962745 | yes | 9.34e−12 |
| −0.12 | −0.14293519435759991794 | yes | 4.24e−11 |
| −0.13 | −0.14170950215217402037 | yes | 4.78e−11 |
| −0.14 | −0.13863892525436206481 | yes | 4.56e−11 |
| −0.16 | −0.12556766421725524015 | yes | 1.73e−11 |

Domain length matters near β → 0⁻: L = 8 is wrong in the 3rd significant digit, L = 10 in the 4th–5th, L = 12 still
off by ≈ 1e−8 at β = −0.04, −0.05; L = 15 agrees with L = 30 to ≈ 1e−18; L = 20, 25, 30 agree to all digits.

### Task 2: statement
- Not vacuous; values off [0, ∞) unconstrained (harmless).
- The fast-approach clause is essential: for β < 0 a slowly (algebraically) decaying far-field mode 1 − p ~ η^{2β}
  exists; without the clause an interval of s near s* would also give p → 1 with |p| ≤ 1.
- Computed profiles meet every clause (q/(1 − p) grows ≈ linearly; min p from −0.122 at β = −0.04 to −0.049 at −0.16).
- Uniqueness scan (`scan_unique.py`, s ∈ [−2, −0.5] step 0.05 and [−0.5, 0) step 0.0025, L = 15 and 20): exactly one
  genuine sign change for s < 0 at each β, at the tabulated value; between it and the blow-up edge solutions overshoot
  p > 1; coarse extra sign changes at −0.05, −0.06, −0.16 (L = 20) were step-size artefacts (finer step: F > 0).
  Numerically, the solution in the class is unique at each β.

### Task 3: printed values
- **Ganapol 2010, arXiv:1006.3888v1, Table 7, p. 23:** all 11 rows agree to all 12 printed significant figures and lie
  in the windows; the other rows (−0.01, −0.02, −0.03, −0.10, −0.15, −0.17, −0.18, −0.19) also agree (`extra_betas.py`).
- **Fazio 2012, arXiv:1212.5057v1, Table 4, p. 30** (own crop `typeset/fazio2012_1212.5057v1_p30_table4.png`): at
  β = −0.05 Stewartson −0.108 and ITM −0.108271 consistent; ITM correct at −0.025, −0.1, −0.15, −0.18. The Stewartson
  column (secondary quote of the 1954 paper, original not checked) prints −0.132 at β = −0.15 (true −0.13342 → −0.133)
  and −0.097 at β = −0.18 (−0.09769 → −0.098); outside this table.
- **arXiv:1907.09912v1, p. 4, Fig. 2 caption** (crop `typeset/belden2019_1907.09912v1_p4_fig2caption.png`; the caption
  claims convergence "within the digits reported"): point V (−0.12, −0.1429351943576) consistent and in our window;
  points II, III consistent; point VI, β = −0.02, prints −0.065168585542904, referee −0.0651685855429030725 (→ …903,
  0.93 units in the last digit; rechecked h = 0.125, N = 34, dps 50, L = 30 and 40); point I, β = 0.5, prints
  0.927680039836653, referee 0.92768003983665114 (≈ 2 units in the last digit).

### Candidate findings
1. Nothing against the frozen rows; Ganapol Table 7 correct to all printed digits.
2. Minor, outside the table: arXiv:1907.09912v1 Fig. 2 caption point VI (β = −0.02) last digit; point I similar.
3. Very minor: Fazio 2012 Table 4 Stewartson column −0.132 at β = −0.15 (should be −0.133).

Files: `fs_taylor.py`, `run_rows.py`, `rows_referee.json`, `scan_unique.py`, `probe_edge.py`, `check_belden.py`,
`extra_betas.py`, two crops in `typeset/`. Downloads outside the repository.
