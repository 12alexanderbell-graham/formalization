# Referee report (Opus subagent, run 2026-11-26T0428Z; saved by the run from the subagent's final message, whose own write was refused)

**STANDS** — the last conjunct says what the docstring says, the numbers are true by a wide margin (actual distances are below 0.07% of the bounds), and the route closes at worst case. One caution: step (c) closes only if the bound on the exp difference is not the crude symmetric mean-value one.

Files read: BRIEF.md and lean/BonnorEbertTurningDecay.lean, nothing else. Scripts in `scripts/`: series.py (series at s = 0), extrema.py (mpmath integrator; out25.txt, out45.txt), scipy_check.py (independent cross-check), table.py (n-table; table_out.txt), route.py (worst-case margins in interval arithmetic; route_out.txt).

## 1. Attack on the statement
- Index convention: n = 0 gives ξ(6)/ξ(5) and (m(ξ6) − c)/(m(ξ5) − c), c = √(2/π); numerator index n+6, denominator n+5, as the docstring says.
- Absolute values and the limit's sign: both bounds use |·|; the second is |Q + e^{−π/√7}|; measured quotients ≈ −0.30501, so the sign is right. Same m as every other conjunct.
- Junk values: none. ξ(n+5) ≥ ξ(0) ≥ 6.45 > 0 by StrictMono; m(ξ_k) − c ≠ 0 by the strict alternation conjunct; √(4π) > 0.
- Vacuity: satisfied by the actual isothermal solution. Bounds 2.3 and 0.15 at n = 0 are weaker than the existing 9.2–12.9 and −0.42…−0.21; from n ≈ 2 on strictly stronger and shrinking geometrically.

## 2. Numbers (own integrator)
Homology system s u' = u(3−u−v), s v' = v(u−1) in t = log s, mpmath Taylor odefun, start s = 1e-4 from the series w = −s²/6 + s⁴/120 − s⁶/1890 + 61s⁸/1632960 − … (truncation ≈ 1e-56); extrema = zeros of g = 2u − v, refined by findroot. dps 25 vs 45 agree to 4e-23 relative in ξ_k and 2e-19 in m − c (k ≤ 13); scipy DOP853 agrees to ≈ 1e-13. ξ0 = 6.450751444….

| k | ξ_k | m − √(2/π) | ε_k = √Nw |
|---|---|---|---|
| 5 | 907946.19315 | −9.2238556e-4 | 3.2707e-3 |
| 6 | 9760974.981 | 2.8142979e-4 | 9.9755e-4 |
| 7 | 1.0491704e8 | −8.5830285e-5 | 3.0427e-4 |
| 8 | 1.1277773e9 | 2.6179907e-5 | 9.2805e-5 |
| 9 | 1.2122527e10 | −7.9850611e-6 | 2.8306e-5 |
| 10 | 1.3030626e11 | 2.4355312e-6 | 8.6337e-6 |
| 11 | 1.4006728e12 | −7.4286095e-7 | 2.6334e-6 |
| 12 | 1.5055956e13 | 2.2658015e-7 | 8.0321e-7 |
| 13 | 1.6183777e14 | −6.9109226e-8 | 2.4499e-7 |

Limits: e^{2π/√7} = 10.7490870292, −e^{−π/√7} = −0.3050100928.

| n | ξ ratio | d1 | d1/(2.3·0.42ⁿ) | Q | d2 | d2/(0.15·0.42ⁿ) |
|---|---|---|---|---|---|---|
| 0 | 10.7506095 | 1.522e-3 | 6.6e-4 | −0.30511080 | 1.007e-4 | 6.7e-4 |
| 1 | 10.7486234 | 4.637e-4 | 4.8e-4 | −0.30497939 | 3.071e-5 | 4.9e-4 |
| 2 | 10.7492285 | 1.415e-4 | 3.5e-4 | −0.30501946 | 9.367e-6 | 3.5e-4 |
| 3 | 10.7490439 | 4.315e-5 | 2.5e-4 | −0.30500724 | 2.857e-6 | 2.6e-4 |
| 4 | 10.7491002 | 1.316e-5 | 1.8e-4 | −0.30501096 | 8.714e-7 | 1.9e-4 |
| 5 | 10.7490830 | 4.014e-6 | 1.3e-4 | −0.30500983 | 2.658e-7 | 1.4e-4 |
| 6 | 10.7490883 | 1.224e-6 | 9.7e-5 | −0.30501017 | 8.107e-8 | 9.8e-5 |
| 7 | 10.7490867 | 3.735e-7 | 7.0e-5 | −0.30501007 | 2.473e-8 | 7.2e-5 |

In practice d1 ≈ 0.465 ε and d2 ≈ 0.031 ε (route: 400 ε, 26 ε); ε_{k+1}/ε_k = 0.30501 ≈ e^{−π/√7} (route: 0.42); ε_5 = 0.00327 ≤ 0.0057.

## 3. Route, worst case (π ∈ [3.141592, 3.141593], √7 ∈ [2.64575, 2.6458], ε = 57/10000)
- L0 = 2π/√7 ∈ [2.374777, 2.374822]; L ≥ 2.221619; L ≤ 2.550667.
- (a) closes: ε_{k+1}/ε_k ≤ exp(−0.882872) = 0.413594 ≤ 0.42; base ε ≤ √(3234e-8) = 0.0056868.
- (b) closes: |L − L0| ≤ 30.858 ε ≤ 31 ε (margin 0.46%); |e^L − e^{L0}| ≤ 362.6 ε sharp, 397.6 ε by the cruder mean-value form e^{L0+31ε}·31ε (still ≤ 400, margin 0.6%).
- (c) closes with a caveat: half the advance of log Nw minus (−π/√7) lies in [−61.34 ε, 53.43 ε]; |u − 1| = ε/√32 ≤ ε/5; R = (u_{k+1}+1)/(u_k+1) ∈ [0.99886, 1.00114]; sharp |Q + e^{−π/√7}| ≤ 19.13 ε. **Gap to watch:** symmetric 62 ε with |e^a − e^b| ≤ e^{max(a,b)}|a−b| written as e^{−π/√7}e^{62ε}·62ε·R + e^{−π/√7}|R−1| gives 27.02 ε > 26 ε. Closes by e^δ − 1 ≤ δe^δ (22.77 ε), by the two sides separately (22.18 ε), or the direct interval (19.13 ε).
- Algebra: Q = (u_{k+1}² − 1)/(u_k² − 1) from m = √(2/π)u² at zeros of g; x_{k+1}/x_k = −√(Nw(b)/Nw(a)).
- (d) closes: 400·0.0057 = 2.28 ≤ 2.3; 26·0.0057 = 0.1482 ≤ 0.15.

No logical gap; the fragility is the bound on exp differences in (c), and less in (b).

## 4. Prior art (background knowledge only, no web lookup)
The limits are classical (linearisation of the homology system at (1, 2): Chandrasekhar 1939, Ebert 1955, Bonnor 1956; Chavanis 2002 A&A 381, 340; Lombardi & Bertin 2001). Asymptotic or numerical only; no explicit non-asymptotic geometric bounds or formal verification known to the referee ("not known to me", not a search result).
