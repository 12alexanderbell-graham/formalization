# Referee report: `Work/FalknerSkan/ReversedRows.lean` (run 2026-11-12T1828Z)

## Verdict: STANDS

All eight statements are correctly posed and, by independent high-precision numerics, true. Every reversed-branch
f''(0) lies strictly inside its ten-decimal window with a margin of at least 1.7e-12, which is about 1e7 times the
numerical error (at most 1e-19). The fast-approach clause selects the right class: without it the windows and
the two-solution claims would hold trivially. No corrections to the statements are needed. The only fixes are
to two figures in the referee brief, listed under "Corrections" below.

## Numerics (own code, nothing reused from `scripts/`)

- `referee_fs.py`: a hand-written Taylor-series integrator (order 24 to 40, step 1/8 or 1/16) in mpmath at
  30, 40 or 60 digits, with secant shooting on s = f''(0). Two far-field conditions are used: (A) f'(L) = 1, and
  (B) a Robin condition that removes the algebraic mode, f'' = (1 - f')(x + (1+2β)/x) with x = f(L).
  The truncation length is L = 10, 12, 14 or 16.
- Results agree to 19 to 22 digits across L ≥ 12, both conditions, step, order and precision. L = 10 with
  condition (A) is off by about 2e-10. That shows L = 10 alone is not safe for the tight margins.
- `referee_check.py`: mpmath `odefun` (a different integrator) at β = -0.17, L = 12, (B) gives -0.11422723909825489649 (20 digits agree).
- `referee_hp.py` reruns at 60 digits, L = 16, order 40. It confirms f' < 1 on all of [0, 16] and that f''
  changes sign exactly once.
- Outputs are in `main_out.txt`, `check_out.txt`, `hp_out.txt` and `scan_*.txt`.

| β | referee f''(0), reversed branch | est. error | window | inside? | margin to nearer end |
|---|---|---|---|---|---|
| -0.15 | -0.13342123789528869657 | < 1e-19 | (-0.1334212379, -0.1334212378) | yes | 4.71e-12 (lower) |
| -0.17 | -0.11422723909825489649 | < 1e-19 | (-0.1142272391, -0.1142272390) | yes | **1.75e-12 (lower)** |
| -0.18 | -0.09769206013457255615 | < 1e-19 | (-0.0976920602, -0.0976920601) | yes | 3.46e-11 (upper) |
| -0.19 | -0.07133590600343803100 | < 1e-19 | (-0.0713359061, -0.0713359060) | yes | **3.44e-12 (upper)** |

Margins to the far end are 9.5e-11, 9.8e-11, 6.5e-11 and 9.7e-11. Error estimate: the largest spread over
L ∈ {12, 14, 16}, conditions A and B, step 1/8 or 1/16, order 24 or 30 and 30 or 40 digits was
9e-17 / 5e-18 / 1e-18 / 2e-19 (in table order). That spread is set by the L = 12, condition A run. The runs
with L ≥ 14 agree to all 22 printed digits.

Solution shape (L = 16, 40 digits; min f' confirmed at 60 digits):

| β | min f' | f' > 0 for η ≳ | f''(16)/(1 - f'(16)) |
|---|---|---|---|
| -0.15 | -0.05954 | 1.81 | 12.3 |
| -0.17 | -0.03841 | 1.38 | 12.7 |
| -0.18 | -0.02649 | 1.13 | 13.0 |
| -0.19 | -0.01339 | 0.81 | 13.2 |

- In every case -1 ≤ f' ≤ 1 holds; f'' > 0 after its only zero (η ≈ 0.4 to 0.9); f''/(1 - f') grows like η
  (the exponential mode).
- At 30 digits there is an apparent second sign change of f'' near η ≈ 14, with f' - 1 ≈ +1e-23. This is an
  artifact: rounding in s excites the algebraic mode. It disappears at 60 digits (`hp_out.txt`).

Attached branch for the `*_two_decay` statements, from the float scan: f''(0) = +0.2163614056, +0.1621146771,
+0.1286362206 and +0.0856997441. In each case f' runs from 0 to 1, so q(0) ≠ q₂(0) by a margin of 0.16 to 0.35.

## Printed values (prior art)

| β | source (typeset crop) | printed | correct to printed digits? |
|---|---|---|---|
| -0.15 | Ganapol 2010, arXiv:1006.3888v1, p.23, Table 7 | -1.33421237895E-01 | yes (12 sig. digits) |
| -0.17 | same | -1.14227239098E-01 | yes |
| -0.18 | same | -9.76920601346E-02 | yes (true ...601345726, rounds to ...601346) |
| -0.19 | same | -7.13359060034E-02 | yes |
| -0.15 | Fazio 2012, arXiv:1212.5057v1, p.30, Table 4, ITM column | -0.133421 | yes |
| -0.18 | same, ITM column | -0.097692 | yes |
| -0.15 / -0.18 | same table, quoting Asaithambi and Auteri et al. | -0.133421 / -0.097692 | yes (secondary quote) |
| -0.15 / -0.18 | same table, quoting Stewartson 1954 | -0.132 / -0.097 | **no**: errors 1.4e-3 and 6.9e-4; correctly rounded values are -0.133 and -0.098 |

- The crops are in `typeset/ganapol2010_1006.3888v1_p23_table7.png` and `typeset/fazio2012_1212.5057v1_p30_table4.png`.
  v1 is the only version of each paper.
- Ganapol's Table 7 is a printed 12-digit value at all four β. Each one equals our value rounded, so the
  windows are consistent with the literature. Each window contains Ganapol's value truncated to 10 decimals.
- Stewartson, Asaithambi and Auteri were not checked in their originals. Those values are typeset-verified only
  as Fazio quotes them.
- Cebeci & Keller 1971 has no rows at these β (Ganapol's Table 8 lists their β as -0.152118, -0.180553).
  Guo et al. (arXiv:2010.05682, Jaya/Runge-Kutta) has no lower-branch f''(0) table. Zhu, Cheng & Wu: not checked.

## Attacks

1. **Literal parsing.** `-0.1142272391 < q 0` parses as `-(OfScientific 1142272391 true 10) < q 0`, which is
   exactly -1142272391/10^10 in ℝ. Unary minus binds tighter than `<`. `(-17 / 100)` is real division and
   equals -0.17 exactly.
2. **Sign convention.** `q' = -(f q) - β(1 - p²)` is f''' = -f f'' - β(1 - f'²), which is correct. Derivatives
   at η = 0 are one-sided via `HasDerivWithinAt _ _ (Ici 0)`, which is fine. The bound -1 ≤ p ≤ 1 is imposed
   only on `Ici 0`. Values for η < 0 are unconstrained, but nothing depends on them.
3. **Vacuity and junk.** The statements are existential with no hypotheses, so there is nothing to make them
   vacuous. There is no division and there are no partial functions. Is p ≡ 1 eventually a possible junk
   witness? No: if p = 1 and q = 0 at any point, ODE uniqueness forces p ≡ 1 everywhere, which contradicts p(0) = 0.
4. **Is the fast-approach clause load-bearing? Yes, and it is essential.**
   - For β < 0 both linear far-field modes of g = 1 - f' decay: g ~ x^{2β} (algebraic) and
     g ~ x^{-1-2β} e^{-x²/2}.
   - Float check at β = -0.15, to η = 400: every s strictly between the two exponential roots (-0.1334, 0.2164)
     gives f' → 1 algebraically with |f'| ≤ 1 (s = -0.13: f'(400) = 0.9987, min f' = -0.0565; s = 0: 0.9808).
     Outside them f' overshoots 1. So the two Stewartson solutions are the endpoints of this continuum.
   - Without the M-clause, every window inside that interval, and the two-solution claim, would be trivially true.
   - With the clause: on algebraic solutions q/(1 - p) ~ -2β/η → 0, which fails for M > 0. Approach from above
     (p > 1) fails for M → -∞. Exponential solutions have ratio ~ η → ∞, which passes.
   - So the clause characterizes exactly the exponentially decaying class, and the window claim is meaningful.
5. **Uniqueness in the class** (numerical evidence, not proof).
   - Scanned s ∈ [-3, 3] with step 0.002 for sign changes of the Robin residual at L = 12 (`referee_scan.py`;
     the β = -0.15 run printed its roots before a tool timeout, so it has no `scan_*.txt` file).
   - Exactly two roots at every β: the reversed root inside the window and the attached root. Both have |f'| ≤ 1.
   - For s ≲ -0.33 to -0.38, |f'| exceeds 5 before η = 12. Large s overshoots f' > 1.
   - So the window singles out Stewartson's lower branch.
6. **Quantifiers.** `∀ M, ∀ᶠ η in atTop, …` lets the threshold depend on M, which is correct.
   `q 0 ≠ q₂ 0` in `two_decay` is the right non-triviality condition. These statements do not use the window,
   and the attached root would also satisfy them.
7. **Tightness risk.**
   - The tightest margin is 1.75e-12 at β = -0.17 (lower end). The β = -0.19 upper margin is 3.44e-12 and the
     β = -0.15 lower margin is 4.71e-12.
   - Any proof must enclose f''(0) to better than about 1e-12, i.e. a verified width of about 1e-12 or less.
     That is demanding but feasible with interval Taylor methods.
   - A float-shooting enclosure built with L = 10 and the far-field condition f'(L) = 1 would already be wrong at
     the 2e-10 level. At β = -0.15 it gives -0.1334212381, which is outside the window.
   - Any certificate must therefore treat the far field rigorously (exponential-mode condition), not by truncation.

## Corrections

- No corrections to the Lean statements.
- The brief says "two windows have margins of about 2e-12". The actual figures are 1.75e-12 (β = -0.17, lower)
  and 3.44e-12 (β = -0.19, upper). Also, β = -0.15 has a 4.71e-12 lower margin, which is tighter than β = -0.19's.
- The file header's "q(0) ≈ −0.13342123790" (float shooting) agrees with ours to 11 decimals:
  -0.133421237895 rounds to -0.13342123790.
