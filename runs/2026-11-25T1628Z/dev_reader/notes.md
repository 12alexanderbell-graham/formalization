# Notes (blind reading)

- Mass inside radius s: integral of 4*pi*s^2 e^w = 4*pi*s^2*(-phi) (since (s^2 phi)' = -s^2 e^w). Pressure is e^w(s), mass scales as P^(-1/2), so m ~ s^2 (-phi) e^(w/2). So P=2, D=2.
- Singular solution w = log(2/s^2): -phi = 2/s, e^(w/2) = sqrt2/s, so s^2(-phi)e^(w/2) = 2*sqrt2 = sqrt8. With the sqrt(4*pi) normalisation, F=4, and the mass is sqrt(8/(4 pi)) = sqrt(2/pi), so G=2.
- Linearisation: w = log(2/s^2) + u(t), t = log s, gives u'' + u' + 2u = 0. Roots (-1 +- i sqrt7)/2: decay rate 1/2, angular frequency sqrt7/2 in t. Consecutive extrema are half a period apart (2 pi/sqrt7 in t), so the ratio is -exp(-(1/2)(2 pi/sqrt7)) = -exp(-pi/sqrt7). N=7.
- Consecutive extrema in the sequence: A=1.

Unsure: F could be 1, 2 or 8 (G = 8/F) under another reading of "normalisation by sqrt(4 pi)"; I chose F=4, G=2 as the literal reading. Did not check numerically that deviations of m track u and u_t with the same rate (expected, since m is a smooth function of u, u_t at leading order).
