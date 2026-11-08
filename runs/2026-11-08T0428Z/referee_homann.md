**VERDICT: STANDS**

No change to the three Lean statements. One optional wording note on the module doc is in section 1.

## 1. Attack on the statements
- **Equation and sign.** q' = -2fq - 1 + p^2 is f''' + 2ff'' + 1 - f'^2 = 0. This is the standard Homann form. It is the axisymmetric reduction of the Weidman/Turner biaxial system f''' + (f+g)f'' - f'^2 + 1 = 0 with f = g (Turner–Weidman, Surrey preprint "Homann_Biaxial_FINAL", read). The far-field condition f' -> 1 and f(0) = f'(0) = 0 are correct.
- **Normalisation.** In this form f''(0) ≈ 1.312. Other scalings print other numbers: a HAM paper (Math. Probl. Eng. 2009, 376174) gives C·sqrt(Re) = 2.6239, which implies f''(0) ≈ 0.9277 = 1.3119/sqrt2. So "1.312" is tied to this normalisation, and the module doc states the equation explicitly, which is enough.
- **Literals.** `1.3119376938 : ℝ` is the exact rational 13119376938/10^10 (OfScientific). There is no division or other partial operation.
- **Vacuity.** The right-hand side is polynomial, so the hypotheses pin down a single trajectory on [0,S] (Picard–Lindelöf and Gronwall). I integrated both starts to η = 6 and neither blows up (f ≈ 5.43 at η = 6, |p-1| < 7e-10, |q| < 1.3e-10). The S = 6 instance is satisfiable. For larger S the instance is either satisfiable or vacuous, which is harmless, since the conclusion only looks at (0, 6].
- **Events.** Under: q(η) < 0 with p < 1 on [0,η]. Over: p(η) > 1 with q > 0 on [0,η]. They are mutually exclusive and are the right shooting events.
  - Under: p rises to 1 - 5.7e-10 and then q changes sign.
  - Over: p crosses 1 while q is still positive.
  - s = 0 in Icc 0 η is harmless because p(0) = 0 < 1 and q(0) > 0.
- **Existence statement.** It asks for a global solution on [0,∞) with p -> 1 and q(0) in the open interval. This matches the doc. It does not assert 0 < p < 1 or q > 0 (the same near-miss as Hiemenz); without uniqueness it says "a solution", not "the physical one". The doc says this honestly.
- **Optional doc wording.** The sentence "no scaling symmetry removes the far-field condition" is fine. I would not claim uniqueness anywhere, since I found no citable proof for the axisymmetric case (section 3).
- **Proof difficulty.** The margins are tiny. α* sits 7.98e-11 above the lower literal and 2.02e-11 below the upper one. In p and q the margins at the recommended witnesses are about 1e-10, so a validated high-order Taylor or interval integrator at 1e-12 absolute accuracy is needed.

## 2. Independent computation
Own code is /tmp/claude-0/referee_tmp/h.py: mpmath at 60 digits, Taylor series of order 44, h = 1/16.
- **Method A, event bisection.** I bisected on the under/over classification, starting from [1.3119376938, 1.3119376939], for 110 steps. The bracket is [1.31193769387980513548164617068342586020890612…, 1.3119376938798051354816461706834258602089061982…].
- **Method B, far-field matching.** Secant on q(L) = (p(L)-1)·u'/u at x = f(L). The decaying mode of u'' + 2xu' - 2u = 0 has the closed form u = e^{-x²} - sqrt(π)·x·erfc(x), and u'/u = 1/x - e^{-x²}/(x·u).

  | L | f''(0) |
  |---|---|
  | 8 | 1.3119376938798051354816461706834258602089061976784870917 |
  | 10 | 1.31193769387980513548164617068342586020890619767848709170814 |
  | 12 | 1.31193769387980513548164617068342586020890619767848709170814 |

- **Result: f''(0) = 1.3119376938798051354816461706834 (about 32 digits).** A and B agree to about 1e-34 (A's bracket has width 1e-34). The true value lies strictly inside the interval, so `homann_exists` is true, provided a global BVP solution exists at this shooting value. Method B's convergence supports that.
- **Distances.** α* - 1.3119376938 = 7.98e-11. 1.3119376939 - α* = 2.02e-11.
- **α = 1.3119376938 (under).** q first hits 0 at η = 5.0841551290, with p = 1 - 5.68e-10.

  | η | p - 1 | q |
  |---|---|---|
  | 5.5 | -6.07e-10 | -1.21e-10 |
  | 6 | -6.68e-10 | -1.23e-10 |

  Witness η = 6 has margins q = -1.2e-10 and 1 - sup p ≈ 5.7e-10. The event time is 0.92 before 6.
- **α = 1.3119376939 (over).** p first exceeds 1 at η = 4.8319371185, where q = 1.22e-9 (still positive).

  | η | p - 1 | q |
  |---|---|---|
  | 5 | +1.09e-10 | +2.97e-10 |
  | 5.5 | +1.53e-10 | +3.3e-11 |
  | 6 | +1.69e-10 | +3.1e-11 |

  Witness η = 5 has margins p - 1 = 1.1e-10 and min q on [0,5] ≈ 3.0e-10. q on [0,6] stays positive with margin of about 3e-11. The event time is 1.17 before 6. This case is tight, since q is nearly 0 around η ≈ 5.5–6, so the witness should be at η ≤ 5.

## 3. Prior art
- **Printed values.** I could not retrieve any source printing f''(0) for Homann flow. The pages I read did not contain it: Wikipedia "Stagnation point flow" (equations stripped, no number), the Turner–Weidman biaxial preprint (no α = β = 0 value), the 2009 HAM paper (gives only scaled skin friction), and a Springer paper on plane flow. From memory, and unverified here, Schlichting–Gersten and White print about 1.312 (4 digits), and Homann (1936, ZAMM 16, 153) tabulated only a few digits. I did not find any source printing ≥ 10 correct digits. This is consistent with a 10-digit certified value being new, but it is not proof of absence.
- **Uniqueness and existence.** I found none specific to the axisymmetric (Homann) problem in what I read. The Hiemenz-report citations (Coppel 1960; Craven–Peletier 1972, for 0 ≤ β ≤ 1) concern the planar Falkner–Skan equation, not f''' + 2ff'' + 1 - f'^2 = 0. I cannot assert that a published proof covers Homann's equation. Do not cite them for it. Treat uniqueness as not established in print by my search; the Lean module correctly does not claim it.
- **Not read.** Homann 1936, Schlichting–Gersten, White (all from memory), and Coppel's and Craven–Peletier's full texts.

## Sources
- https://personalpages.surrey.ac.uk/m.turner/Homann_Biaxial_FINAL.pdf (read)
- https://emis.univie.ac.at/journals/HOA/MPE/Volume2009/376174.pdf (read)
- https://en.wikipedia.org/wiki/Stagnation_point_flow (read)
- https://doc.rero.ch/record/319336/files/707_2011_Article_502.pdf (read)
