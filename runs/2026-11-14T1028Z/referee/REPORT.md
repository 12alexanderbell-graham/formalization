# Referee report (run 2026-11-14T1028Z): `bonnor_ebert_second_max` — copied verbatim by the main session from the referee's final message (its Write was refused)

**Verdict: STANDS.** Every numeric window contains the true value (two independent methods, 20 digits); nothing to correct.

## Independent values (method B: mpmath Taylor in t = log ξ, 40 and 50 digits, agree in 20 digits; method A: scipy DOP853, agrees to 10–12 digits)

| extremum | ξ | m | contrast e^{−w} |
|---|---|---|---|
| max 1 | 6.4507514441740736585 | 1.1822265884995997255 | 14.042032048640777763 |
| min 1 | 67.007548719595239719 | 0.69436652112855537885 | 2579.6973304538922809 |
| max 2 | 733.76924368659781205 | 0.83069005827551933842 | 258577.1004705434705 |
| min 2 | 7849.6320485004 | 0.78799418792767 | 3.11950474756e7 |
| max 3 | 84506.328975745 | 0.80091195007850 | 3.55716298248e9 |
| min 3 | 907946.19315371 | 0.79696217523850 | 4.12660196057e11 |

- Curve to ξ = 10⁶: oscillates with shrinking swings toward √(2/π) = 0.7978845608.
- sup of m over ξ ≥ ξ₂, |ξ − ξ₃| ≥ 1: m(ξ₃ + 1) = 0.830689994320 (6.4e−8 below m(ξ₃)); away from ξ₃ the largest values are m(2000) = 0.80957 and max 3 = 0.80091.
- Homology variables at ξ = 2000: u = 0.980496205743683875, v = 2.0327898293163244702, V(2000) = 4.585998021264355e−4.
- Max of u v³ on {V ≤ V(2000)}: 8.587023419 against 4π m(ξ₃)² = 8.671373437 (ratio 0.99027), so m ≤ 0.82664 beyond 2000.

## Attack (summary)
Signs (w = −ψ, contrast e^{−w}), mass formula (u v³ = 4π m²), one-sided derivatives on [0, S], φ continuous at 0 (forces φ(0) = 0 and the unique regular solution), no junk values (2/s only for s > 0), "every S ≥ 2000" equivalent to every radius ≥ ξ₂, ξ₁, ξ₂, ξ₃ each fixed by its strict clause, not vacuous, not trivial. Cosmetic: the contrast is 2.586·10⁵ (docstring "≈ 2.59 · 10⁵").

## Prior art (limited search; values read by WebFetch UNVERIFIED)
Chavanis 2002 (arXiv astro-ph/0103159) and cond-mat/0107345: turning points of other quantities and asymptotic forms only, no values near 734, no enclosure. Tohline's Bonnor–Ebert page: first third read, no table of extrema. Not read: arXiv 1511.03457, astro-ph/0208416, 2202.12092, 0809.1457, 1301.0240, and the classical tables (Bonnor 1956, Lynden-Bell & Wood 1968, Padmanabhan 1990). No printed value of ξ₃, m(ξ₃) or the contrast found, no rigorous enclosure, no proof of the maximality statement.

Scripts: `scripts/be_taylor.py` (method B), `scripts/be_scipy.py` (method A, homology checks).
