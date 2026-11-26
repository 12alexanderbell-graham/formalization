# Referee report (Opus, run 2026-11-26T1028Z), saved by the run from the referee's final message

VERDICT: STANDS. The last conjunct says what the docstring says, nothing in it is vacuous, high-precision numerics satisfy every bound with a wide margin, and every route constant holds in the worst case. The tightest margin is step (a): 0.3297 against 0.33.

Files read: only `runs/2026-11-26T1028Z/referee/BRIEF.md` and `runs/2026-11-26T1028Z/lean/GelfandTurningDecay.lean`. No Lean, no web lookup.
Scripts: `scripts/turning.py` (numerics), `scripts/route.py` (worst-case margins, mpmath interval arithmetic).

## 1. Attack on the statement
- Index convention: n = 0 gives |ζ(7)/ζ(6) − exp(2π/√7)|, matching the docstring and the module doc ("at index n + 6").
- Parsing: `2 * Real.pi / Real.sqrt 7` is (2π)/√7; `- -Real.exp (-(π/√7))` is +exp(−π/√7), so the second distance is to −exp(−π/√7) with the correct sign; numerator λ(ζ(n+7)) − 2, denominator λ(ζ(n+6)) − 2 ("next over current"); absolute values on both.
- Junk values: none (ζ(k) > 0 since ζ(0) ≥ 4.07 and ζ strictly increasing; λ(ζ(k)) − 2 ≠ 0 by λ(ζ(2k+1)) < 2 < λ(ζ(2k))).
- Vacuity: none. q = 0 would need equality for n ≥ 1 (false); n = 0 forces c₁, c₂ ≥ 0, so the existential form is equivalent to the concrete bounds c₁ = 47/100, c₂ = 3/100, q = 33/100.

## 2. Independent numerics
Power series of w at 0 to s = 0.25, then a Taylor-series integrator for s u' = u(3 − u − v), s v' = v(u − 1) in t = log s; turning points are roots of v = 2 (Newton on the local series). Two runs (40 digits, h = 0.05, order 30; 50 digits, h = 0.025, order 40) agree to 3e-34 (ζ) and 1.4e-40 (λ).
ζ₀ = 4.07149684430, λ(ζ₀) = 3.32199211834, ζ₆ = 5652734.13 ≥ 300000, ε₆ = √Nw(ζ₆) = 1.311074e-3 ≤ 1.386e-3.
ζ₁ … ζ₁₃ = 37.5268, 428.913, 4532.15, 48978.4, 525619.6, 5652734.1, 6.07525e7, 6.53065e8, 7.01975e9, 7.54562e10, 8.11084e11, 8.71842e12, 9.37150e13 (ζ₁₄ ≈ 1.0e15, ζ₁₅ ≈ 1.1e16). exp(2π/√7) = 10.7490870292, −exp(−π/√7) = −0.3050100928.

| n | dist1 | dist1 / (0.47·0.33ⁿ) | dist2 | dist2 / (0.03·0.33ⁿ) |
|---|---|---|---|---|
| 0 | 1.625e-3 | 0.0035 | 4.612e-5 | 0.0015 |
| 1 | 4.958e-4 | 0.0032 | 1.407e-5 | 0.0014 |
| 2 | 1.512e-4 | 0.0030 | 4.291e-6 | 0.0013 |
| 3 | 4.612e-5 | 0.0027 | 1.309e-6 | 0.0012 |
| 4 | 1.407e-5 | 0.0025 | 3.992e-7 | 0.0011 |
| 5 | 4.291e-6 | 0.0023 | 1.218e-7 | 0.0010 |
| 6 | 1.309e-6 | 0.0022 | 3.714e-8 | 0.0010 |
| 7 | 3.992e-7 | 0.0020 | 1.133e-8 | 0.0009 |
| 8 | 1.218e-7 | 0.0018 | 3.455e-9 | 0.0008 |

True decay ≈ 0.305 per step; the bounds are loose by a factor of about 300 to 1000.

## 3. Route, worst case (π ∈ [3.141592, 3.141593], √7 ∈ [2.64575, 2.6458], ε ≤ 1386e-6)
- (a) ε_{k+1} = ε_k e^{D/2} ≤ ε_k exp(−(1 − 36ε)π/(√7 + 32ε)); exponent ≥ 1.109543, factor ≤ 0.329710 ≤ 0.33 (margin 2.9e-4), consistent with exp(−1.1094).
- (b) |L − 2π/√7| ≤ 32πε/(7/2 − 16√7ε) ≤ 29.25ε ≤ 30ε; with both exponentials ≤ 11.2, 336ε.
- (c) |D/2 + π/√7| ≤ |L/2 − π/√7| + 18ε·L_max ≤ 58.10ε ≤ 59ε; with both exponentials ≤ 0.33, 19.47ε ≤ 20ε.
- (d) 336·1386e-6 = 0.465696 ≤ 0.47; 20·1386e-6 = 0.02772 ≤ 0.03.
- Gaps: none in the arithmetic. The proof must use that consecutive turning points are consecutive zeros of v − 2 (the segment facts are stated for consecutive zeros); the module doc says `radii_main` already supplies the segment bounds at every turning point.

## 4. Prior art (from memory, not checked online)
The focus at (u, v) = (1, 2) with eigenvalues (−1 ± i√7)/2 is classical (Gelfand; Joseph–Lundgren 1973) and gives the ratios only as limits. No known source states explicit non-asymptotic constants such as c·0.33ⁿ for consecutive turning points of the radial Gelfand/Bratu branch in the 3-ball, and no formal verification.

Corrections: none required.
