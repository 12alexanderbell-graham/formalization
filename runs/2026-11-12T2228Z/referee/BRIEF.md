# Referee brief, run 2026-11-12T2228Z (reversed-flow Falkner–Skan table rows)

You are an independent referee. Attack the frozen claims below; do not trust the program.

## The frozen claims (`Work/FalknerSkan/ReversedTable.lean`, read only that file and this brief)
For each β in the table, there is a solution (f, p = f', q = f'') of the Falkner–Skan equation
f''' + f f'' + β(1 − f'²) = 0 on [0, ∞) with f(0) = 0, f'(0) = 0, f' → 1, −1 ≤ f' ≤ 1 and, for every M, eventually
M(1 − f') ≤ f'' (approach to the edge faster than every exponential), whose wall shear f''(0) lies in the stated open
ten-decimal window (negative: reversed flow at the wall, the "second" / lower branch, −0.1988… < β < 0).

| β | window for f''(0) |
|---|---|
| −0.04 | (−0.0966367875, −0.0966367874) |
| −0.05 | (−0.1082710833, −0.1082710832) |
| −0.06 | (−0.1179241111, −0.1179241110) |
| −0.07 | (−0.1258585318, −0.1258585317) |
| −0.08 | (−0.1322276544, −0.1322276543) |
| −0.09 | (−0.1371138119, −0.1371138118) |
| −0.11 | (−0.1425079104, −0.1425079103) |
| −0.12 | (−0.1429351944, −0.1429351943) |
| −0.13 | (−0.1417095022, −0.1417095021) |
| −0.14 | (−0.1386389253, −0.1386389252) |
| −0.16 | (−0.1255676643, −0.1255676642) |

## Tasks
1. Independent high-precision computation (your own code: e.g. mpmath Taylor series or an arbitrary-precision
   integrator; not scipy at default tolerances) of the reversed-flow wall shear at each β, to ≥ 15 significant digits,
   with a convergence study in the far-field length (the profile of the reversed branch gets long as β → 0⁻: check
   that your domain is long enough). State the distance from each value to the nearer window end.
2. Is the frozen statement the right one? Quantifiers, the class (fast approach), junk values, anything vacuous or
   trivially true; is the reverse-flow solution in that class unique at each β (numerical scan of f''(0) < 0)?
3. Printed values: Ganapol 2010 (arXiv:1006.3888v1) Table 7 p. 23 — a typeset crop is at
   `runs/2026-11-12T1828Z/referee/typeset/ganapol2010_1006.3888v1_p23_table7.png`: compare each row. Then look for
   OTHER published reverse-flow (lower-branch) wall-shear values at any of these β (e.g. Stewartson 1954, Fazio 2012
   arXiv:1212.5057 Table 4, Asaithambi, Zhu–Cheng–Wu, Libby & Liu, Cebeci & Keller, Rajagopal et al., textbooks);
   for each printed value give source, page/table, the value, and whether it lies in (or rounds consistently with)
   our window. A printed value that is wrong beyond its printed precision is a candidate finding: say so clearly and
   give a typeset crop.
   Rules: arxiv.org/pdf only (`curl -sSfL -o p.pdf https://arxiv.org/pdf/<id>v<N>`), NO ar5iv, NO arxiv e-print,
   no mirrors. Downloaded PDFs, full-page renders and text dumps go to a temp dir OUTSIDE the repository; only crops
   (≤ 200 KB each, PNG) go into `runs/2026-11-12T2228Z/referee/typeset/`. A transcription from a summarised web page
   is UNVERIFIED until read from the typeset page; if a source prints numbers computed from a formula, reproduce them.
4. Write `runs/2026-11-12T2228Z/referee/REPORT.md`: verdict STANDS / STANDS-WITH-CORRECTIONS / FAILS per row, your
   values, margins, uniqueness scan, printed-value table, candidate findings. Put your scripts in
   `runs/2026-11-12T2228Z/referee/`. Do not edit anything else in the repository, do not commit.
