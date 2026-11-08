# Referee report: Work/Math/LaneEmden2.lean (laneEmden2_constants)

Verdict: STANDS

## 1. Attack on the statement
- Satisfiability: the true regular solution (series 1 - xi^2/6 + ...) exists on [0,5]. I integrated it numerically: theta(5) = -0.0719, theta'(5) = -0.0976, so there is no blow-up and the domain [0,5] works. It is analytic, so theta is differentiable on [0,5] (one-sided at the ends), phi = theta', and phi is continuous at 0. The Lean existence theorem is still "to do", so the formal statement is not yet shown non-vacuous. Mathematically it is not vacuous.
- Strength of the hypotheses: the ODE gives (xi^2 phi)' = -xi^2 theta^2 on (0,5]. Continuity of phi at 0 together with continuity of theta forces xi^2 phi -> 0. Hence phi(xi) = -xi^-2 * int_0^xi s^2 theta^2 ds, and phi(0) = 0 follows (theta'(0) = 0 is derived, not assumed). The integral equation has a Lipschitz fixed point, so the solution is unique. Differentiability of theta at 0 already rules out the singular family theta' ~ C/xi^2, so hphi0 is partly redundant but harmless. The conclusion follows from uniqueness plus the true constants.
- Junk values: the ODE is only asserted for xi in Ioc 0 5, so there is no division by 0 in the hypothesis. In the conclusion, xi1 ~ 4.35 > 0 and the denominator 3*omega2 ~ 7.23 > 0, so no division junk. At xi = 5 the within-Icc derivative is one-sided and is fine.
- "First zero": the conclusion asserts theta(xi1) = 0 and theta > 0 on Ico 0 xi1, which is exactly the first zero. The existential also pins xi1 to a 1e-10 interval, so it is the unique first zero.
- Quantifiers: they are correct (forall theta, phi, then exists xi1). Because of uniqueness, the "exists" is not weaker than the intended claim. The bounds on omega2 and on the ratio are stated for the same xi1, as intended. Not trivial or vacuous in the mathematical sense.
- Minor remark: the docstring says "Only Mathlib definitions"; this is true. The decimal literals are real numerals, which is fine.

## 2. Independent computation (mpmath, 50 digits)
Series start at xi = 0.5 (60 terms), then:
- Method 1: mpmath odefun (tol 1e-40) with findroot.
- Method 2: my own order-50/60 Taylor analytic continuation, steps h = 1/8 and 1/16, Newton for the zero inside the last step. The two step sizes agree to about 1e-47.

| quantity | value |
|---|---|
| xi1 | 4.35287459594612467697357006152614262811236 |
| omega2 = -xi1^2 theta'(xi1) | 2.41104601209689378364844274467140289186944 |
| xi1^3/(3 omega2) | 11.4025428619512616631266845762423448198510 |

The two methods agree to about 1e-39 in every case, and the Taylor runs agree with each other to 1e-47.

Margins of the printed bounds (value - lower, upper - value):
- xi1 in [4.3528745959, 4.3528745960]: 4.61e-11 and 5.39e-11
- omega2 in [2.4110460120, 2.4110460122]: 9.69e-11 and 1.03e-10
- ratio in [11.402542860, 11.402542864]: 1.95e-9 and 2.05e-9

All margins are positive and are far larger than the numerical error (~1e-39). The bounds are true.

## 3. Prior art
- I found no rigorous interval or computer-assisted enclosure of the n = 2 Lane-Emden constants. The WebSearch hits were arXiv 1607.04619 (Dirichlet problems on a square with p in (1,2); I read it: it has no radial IVP, no p = 2, no first-zero enclosure) and various series/Pade/perturbation papers (astro-ph/0107395, astro-ph/0402130, 1708.07384), which I did not read. This is absence of evidence from a short search, not proof of absence.
- Boyd 2011 (Chebyshev Spectral Methods and the Lane-Emden Problem, NMTMA 4): I read only a truncated excerpt. It printed the exact cases m = 0, 1, 5 and claims at least ten digits with N = 100; the n = 2 digits were not in what I read, so "not read". Its approach is numerical, not interval-rigorous.
- Chandrasekhar 1939 Table 4 and Horedt 1986: not read (no accessible source). From memory only, the n = 2 row is about xi1 = 4.35287, -xi1^2 theta' = 2.41105, and rho_c/rho_mean = 11.4025. This is unverified recall and consistent with my values.
