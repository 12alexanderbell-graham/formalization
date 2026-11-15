# Singular Gelfand parameter in the 3D ball

Radial equation: u'' + (2/r) u' + lambda e^u = 0, 0 < r <= 1, u(1) = 0.

Ansatz u = -2 ln r + c. Then u' = -2/r and u'' = 2/r^2, so
u'' + (2/r) u' = 2/r^2 - 4/r^2 = -2/r^2.
Also lambda e^u = lambda e^c / r^2.
The equation holds iff lambda e^c = 2.
The boundary condition u(1) = c = 0 gives lambda = 2.

Check: u = -2 ln r, so u(1) = 0, u -> +infinity as r -> 0 (a multiple of log r), and
Delta u + 2 e^u = -2/r^2 + 2/r^2 = 0 for r > 0.
In general dimension N >= 3 the same ansatz gives lambda = 2(N-2); N = 3 gives 2.

Unsure of: nothing significant. I did not run Python, since the check is a one-line computation by hand.
I read nothing else in the repository and used no web tools.
Uniqueness ("exactly one value") is taken from the brief. The ansatz shows lambda = 2 works.
Other singular profiles would need a different asymptotic, so the brief's "multiple of log r" selects this one.
