# Referee report (run 2026-11-14T1428Z), copied verbatim in substance from the referee's final message (its own write of this file was refused)

**Verdict: STANDS.** Read only BRIEF.md and lean/BonnorEbertMin2.lean; scripts a_scipy.py, b_mpmath.py, b_mpmath40.py.

1. Attack: sign conventions, mass formula (4π m² = u v³; dm = 0 iff v = 2u), one-sided derivatives, φ continuous at 0 (forces φ(0) = 0; needed and sufficient), non-vacuous, non-trivial; S ≥ 20000 equivalent to every radius ≥ ξ₃; joint choice of ξ₁…ξ₄ harmless (each unique); windows printed correctly and contain the true values.

| quantity | true value | window |
|---|---|---|
| ξ₁ | 6.45075144417 | [6.4507514, 6.4507515] |
| ξ₂ | 67.0075487196 | [67.0075, 67.0076] |
| ξ₃ | 733.769244 | [733.5, 734] |
| ξ₄ | 7849.632049 | [7849.5, 7849.75] |
| m(ξ₄) | 0.7879941879 | [0.787992, 0.787995] |
| e^{−w(ξ₄)} | 31195047.48 | [31193900, 31196100] |

Proof note: the minimum is flat (m(ξ₄ ± 1) − m(ξ₄) ≈ 1.58e-10); a proof needs the sign of v − 2u, not value comparisons.

2. Independent computation (scipy DOP853 in log s at rtol 1e-12…3e-14; mpmath odefun at 30 and 40 digits; agree to ≥ 11 digits):

| extremum | ξ | m | e^{−w} |
|---|---|---|---|
| max 1 | 6.4507514441740736585 | 1.1822265884995997255 | 14.042032048640777763 |
| min 1 | 67.007548719595239719 | 0.69436652112855537885 | 2579.6973304538922809 |
| max 2 | 733.76924368659781205 | 0.83069005827551933842 | 258577.1004705434705 |
| min 2 | 7849.6320485004269309 | 0.78799418792767269718 | 31195047.475608645634 |
| max 3 | 84506.3289761 | 0.800911950079 | 3.5571629825e9 |
| min 3 | 907946.193132 | 0.796962175239 | 4.1266019604e11 |

Limit √(2/π) = 0.7978845608; spacing factor ≈ 10.7 (e^{2π/√7} ≈ 10.75). 4π m(ξ₄)² = 7.8028973294. Infimum of m over {ξ ≥ ξ₃, |ξ − ξ₄| ≥ 1} = m(ξ₄) + 1.58e-10. At ξ = 20000: u = 1.0056876608886, v = 1.9890782258127, V = 4.60439742392e-5; min of u v³ on {V ≤ V(20000)} = 7.82179994362 (on v − 2 = 3(u − 1)), above 4π m(ξ₄)² by 0.0189.

3. Prior art (limited search; WebFetch values UNVERIFIED): Chavanis astro-ph/0103159 (canonical-ensemble extrema of βGM/R, not the fixed-pressure mass; no enclosures); Tohline LimitingMasses page not read (verification page), mirror gives only the first maximum. No printed position, value or contrast of the second minimum found at any precision; no rigorous enclosure of any Bonnor–Ebert extremum found; no proof that the second minimum is the smallest mass beyond the second maximum. Negative result of a limited search.

4. STANDS. Caveat: the import `Checked.Math.BEH2Main` was outside the audit.
