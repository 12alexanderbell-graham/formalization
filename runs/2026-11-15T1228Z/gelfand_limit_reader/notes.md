# Notes: limit of the radial Gelfand branch, n = 3

A = 2.

Derivation. Try u = ln(c/r^2) = ln c - 2 ln r. Then u' = -2/r, u'' = 2/r^2, so
u'' + (2/r) u' = 2/r^2 - 4/r^2 = -2/r^2. Also lambda e^u = lambda c / r^2.
The equation holds iff lambda c = 2. The boundary condition u(1) = 0 gives c = 1, so lambda = 2
(in general 2(n-2) for dimension n, which is 2 for n = 3). In terms of w, the regular solution
satisfies w(s) = ln 2 - 2 ln s + o(1), so s^2 e^{w(s)} -> 2.

Numerical check (scipy solve_ivp, rtol 1e-12, start s=1e-6, w=w'=0, run to s=1e4):
s=10: 2.3836; s=100: 1.8483; s=1e3: 2.0533; s=1e4: 1.9817.
It oscillates around 2 with decaying amplitude, as the brief describes.

Unsure of: nothing substantive. No web sources were used (none read). Only the brief was read in the repository.
