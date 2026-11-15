# Referee report (run 2026-11-15T1228Z), returned as text (the harness refused the subagent's file write); saved verbatim in substance by the main session

**Verdict:** statement STANDS; route STANDS-WITH-CORRECTIONS (one gap claimed, see below).

## 1. The statement
- The hypotheses fix one solution: (s²φ)' = −s²e^w and φ continuous at 0 give s²φ(s) = −∫₀ˢ t²e^w dt, so φ(0) = 0 and the integral equation has a unique global solution.
- Not vacuous; values at s < 0 never used (every s in the conclusion is ≥ 0 or ≥ ζ(2k) > 0).
- Map to Gelfand solutions right: u(r) = w(sr) + log(s²/λ) gives u'' + (2/r)u' = −λe^u, u(1) = 0 iff λ = s²e^{w(s)} (same as u = w(sr) − w(s)).
- Indexing and signs right: λ(0) = 0, v ≈ s²/3 < 2 near 0, so the first turning point is a maximum (even = maxima).
- "Strict extreme from the previous one on" conjuncts true: maxima decrease, minima increase, max > 2 > min, λ → 2.
- No other critical point: monotone on [0, ζ₀] and each [ζ_j, ζ_{j+1}], which cover [0, ∞) because ζ → ∞ (stated separately, as needed).
- Windows contain the computed values: ζ₀ = 4.0714968442981 (≈ 3e-10 inside the lower end), λ* = 3.3219921183398 (≈ 3.4e-10 inside the lower end).
- No defect found in the statement.

## 2. The planned route
Checked by hand, all correct: λ' = s e^w (2 − v); v' = φ + s e^w = −φ(u − 1); u v = λ; s u' = u(3 − u − v), s v' = v(u − 1), equilibrium (1, 2); Volterra derivative −(u − 1)²/s; at a zero of D = 2e^w − φ², D' = (2φ²/s)(2 − v); φ < 0 for s > 0; 4πm² = u v³ = s⁴e^wφ², critical points of m are the zeros of D.
Logic: ordering of extrema (u > 1 at maxima, u < 1 at minima, Volterra strictly decreasing), sign change after every radius (one fixed strict sign of D' at every zero of D past R contradicts infinitely many mass extrema), limit (4πm² = 8u at turning points, m → √(2/π)) — correct.
**Claimed gap:** excluding the equilibrium (u, v) = (1, 2) at some s₀: "4πm² = 8 there" only makes s₀ a critical point of m, not one of the listed extrema; needed for transversality, strict decrease of V and D' ≠ 0. Proposed fix: ODE uniqueness against the singular solution log(2/s²).
Minor: write out finiteness of turning points on compacts and ζ → ∞.

## 3. Independent computation (two methods agree)
Method A: scipy DOP853 in t = log s (x = log λ, y = sφ), rtol 2.2e-14, events y = −2. Method B: mpmath odefun (Taylor, 30 digits) on the homology system, roots of v − 2 by findroot.

| k | type | ζ_k (B) | λ(ζ_k) (B) |
|---|---|---|---|
| 0 | max | 4.07149684429813935 | 3.32199211833982399 |
| 1 | min | 37.5267987393168607 | 1.66415618975679522 |
| 2 | max | 428.912529082209273 | 2.10854110210643008 |
| 3 | min | 4532.14861911681606 | 1.96746555866859268 |
| 4 | max | 48978.3931097060503 | 2.00997640496697766 |
| 5 | min | 525619.598125567309 | 1.99696203628253425 |

A matches all 12 digits it prints; ζ₆ ≈ 5.6527e6 (λ ≈ 2.000927), ζ₇ ≈ 6.0753e7 (λ ≈ 1.999717). 2 − v changes sign exactly 8 times on 2·10⁶ grid points up to 1e8; u − 1 at the roots 0.661, −0.168, 0.054, −0.0163, 0.0050, −0.0015 (transversal). ζ_{k+1}/ζ_k ≈ 10.7 (half-period 2π/√7 in log s).

## 4. Prior art
Not read (WebSearch denied by the permission system; no workaround). From memory, UNVERIFIED: Joseph & Lundgren (ARMA 49, 1973) prove for 3 ≤ N ≤ 9 the radial branch oscillates around λ = 2(N − 2) with infinitely many turning points; Gelfand (1959/1963) treats N = 3; λ* ≈ 3.32 widely quoted to 2–4 digits; no source known to print λ at the later turning points.

## Main session's note on the claimed gap
The route does not use "4πm² = 8 at s₀" alone: if (u, v) = (1, 2) at s₀ then Volterra's H(s₀) = 0, H ≥ 0 and H antitone force H ≡ 0, hence (u, v) ≡ (1, 2), on [s₀, ∞), so m ≡ √(2/π) there, contradicting the strict band m(ξ(2k)) > √(2/π) at some ξ(2k) > s₀. This is how `Work/Math/GelfandExtremaMain.lean` proves it (Lean-checked); the referee's ODE-uniqueness fix is an alternative.
