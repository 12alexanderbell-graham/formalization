# Referee report (run 2026-11-15T0828Z): `bonnor_ebert_extrema_monotone`

Copied by the main session from the referee subagent's final message (its own write was refused by the harness). Model output, unchecked prose.

**Verdict: STANDS.** Statement faithful (w = −ψ, φ = w', mass ξ²ψ'e^{−ψ/2}/√(4π), even = maxima, odd = minima, the monotonicity conjuncts on the same sequence as the extremal ones); hypotheses force the unique regular solution (one-sided derivatives unique on Ici 0; φ continuous at 0 gives s²φ = −∫₀ˢ t²e^w), which exists for all s, so not vacuous; no junk values (m(0) = 0 whatever φ(0)). The monotonicity conjuncts force the ξ's to be exactly the local extrema of m on (0, ∞).

Independent computation: dm/ds = s²(e^w − φ²/2)e^{w/2}/√(4π), so sign m' = sign(2u − v) (u = ξe^w/(−w'), v = −ξw', d ln m²/d ln ξ = 2u − v). Method 1 (scipy DOP853 in ξ, rtol 1e−13, ≈ 6·10⁶ samples of 2e^w − φ² on [1e−3, 3e6], series on [0, 1e−3]: ≥ 1.9999995) and method 2 (mpmath Taylor at 30 digits on (u, v), t = ln ξ, 6000-point grid + findroot): exactly six simple sign changes up to 3e6, agreeing to ≈ 12 digits.

| k | type | ξ_k | m(ξ_k) | m − √(2/π) | d(2u−v)/dt |
|---|---|---|---|---|---|
| 0 | max | 6.45075144417 | 1.18222658850 | +3.843e−1 | −2.116 |
| 1 | min | 67.0075487196 | 0.69436652113 | −1.035e−1 | +0.501 |
| 2 | max | 733.769243687 | 0.83069005828 | +3.281e−2 | −0.166 |
| 3 | min | 7849.63204850 | 0.78799418793 | −9.890e−3 | +0.0494 |
| 4 | max | 84506.3289757 | 0.80091195008 | +3.027e−3 | −0.0152 |
| 5 | min | 907946.193154 | 0.79696217524 | −9.224e−4 | +0.00462 |

Minimum |2u − v| on the inner 90 % of each interval: 1.67, 0.062, 0.022, 0.0063, 0.0020, 0.00058, 0.00027 (∝ e^{−t/2}). Tail: Jacobian at (1, 2) has eigenvalues (−1 ± i√7)/2, no real eigenvector, so the line v = 2u is crossed transversally twice per turn.

Prior art (WebFetch, UNVERIFIED): the criterion d ln m / d ln ξ = (2u − v)/2 is folklore-level in Milne variables; Chavanis astro-ph/0103159 (box-confined, extrema of a different quantity at u₀ = 1); Ball, Tout & Żytkow 1201.5560 (no monotonicity claim); Chavanis astro-ph/0207080 not read (WebFetch denied). No rigorous proof in print that m is strictly monotone between consecutive turning points for every k found.
