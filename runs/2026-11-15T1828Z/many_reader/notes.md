# Notes (many_reader)

Setting: D = 3 (ball in 3-dim Euclidean space), centre C = 0.

Singular solution: u = -2 ln r + c. In 3D, u' = -2/r, u'' = 2/r^2, so Δu = u'' + 2u'/r = -2/r^2. And e^u = e^c / r^2. The equation Δu + λ e^u = 0 needs λ e^c = 2; u(1) = 0 gives c = 0, so λ = 2. Check: -2/r^2 + 2·(1/r^2) = 0. S = 2.

Reduction: with u(r) = w(kr) - w(k), u'' + 2u'/r = k^2 (w'' + 2w'/s)(kr) = -k^2 e^{w(kr)} = -k^2 e^{w(k)} e^{u}. So λ = k^2 e^{w(k)}, u(1) = 0, and w(0) = w'(0) = 0 gives u regular at the centre. Check: the Taylor series of w starts w = -s^2/6 + ...
Critical point: d/ds[s^2 e^w] = e^w s (2 + s w') = 0, i.e. 2s + s^2 w' = 0.

Computation: series for w at 0 (60 terms, via e^w recurrence), evaluated at s0 = 0.1 as the start, then mpmath odefun (Taylor method with step control), root found by Anderson bracketing on [1.5, 3] in the function 2s + s^2 w'(s) (note: its first root is the maximiser, s* ≈ 4.0715; the scan shows the function is positive on 0.5..4, so s* ≈ 4.07 is the first and only maximum). Hmm, correction: the bracket [1.5, 3] is only the starting pair; the solver converged to the root near 4.0715, where the sign change is (F(4) = 0.0945 > 0, F(5) = -1.20 < 0). Maximum is the first sign change since F > 0 on (0, 4).
Results:
- 30 digits: s* = 4.07149684429813934760120903334, λ* = 3.321992118339823988416478082
- 45 digits: s* = 4.07149684429813934760120903334471607528537176, λ* = 3.32199211833982398841647808200299556903365878
These agree to ≥ 28 digits (different working precision and tolerances). Independent scipy DOP853 (rtol 1e-13) gives s* ≈ 4.0715 (F ≈ -4e-6 at 4.0715, consistent) and s^2 e^w = 3.32199211834 there.
Error estimate: well below 1e-25; the ninth digit is decided.

λ* ≈ 3.32199211833982...; L = 3.321992118 (digits after the decimal point: 321992118|339..., rounded down).

Unsure: nothing material. I did not use any web source or book for λ* or S. (I recalled a figure 3.5138 vaguely, but my computation does not support it for the 3D ball; I trust the computation.)
