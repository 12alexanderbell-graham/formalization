# Referee report: GelfandTurningRadii (run 2026-11-25T1028Z)

(Opus subagent, ≈ 3 min; its Write of this file was refused, so the program saved its final message here verbatim in substance. Scripts and outputs: `scripts/`.)

VERDICT: STANDS. The statement says what its docstring says and ζ is uniquely pinned. The numbers are right, with true values far inside the intervals, and the planned route gives all four bounds. The tightest route margin is 2.98e-4, on the bound −0.33.

## 1. Attack on the statement
- The last two conjuncts match the docstring: Tendsto ζ(k+1)/ζ k → exp(2π/√7); for every k ≥ 6, 10.3 ≤ r ≤ 11.2 and −0.33 ≤ q ≤ −0.28 (r = ζ(k+1)/ζ(k), q = (λ(ζ(k+1))−2)/(λ(ζ(k))−2)). Directions correct, q correctly negative; ζ 6 is the seventh turning point.
- ζ is pinned uniquely by induction on the conjuncts (ζ 0 unique global maximiser of λ on [0,∞); ζ(2k+1) unique minimiser on [ζ(2k),∞); ζ(2k+2) unique maximiser on [ζ(2k+1),∞)).
- Each ζ k (k ≥ 1) is a zero of y = v−2 and every zero of y is a turning point (a tangential zero would need the equilibrium).
- No junk values: ζ k ≥ 4.07 > 0; λ(ζ k) − 2 ≠ 0 by λ(ζ(2k+1)) < 2 < λ(ζ(2k)).
- The hypotheses force the regular solution (φ(0) = c ≠ 0 gives φ ~ −2c log s, contradicting continuity at 0).
- No defects found.

## 2. Numerical check
Power series of W in s² to 400 terms, then a Taylor-series integrator for s u' = u(3−u−v), s v' = v(u−1) in t = log s; turning points at v = 2 by bisection plus Newton, λ = 2u there. Three runs (dps, order, h, s0) = (40, 40, 0.05, 0.5), (50, 50, 0.1, 1.0), (60, 30, 0.03, 0.3) agree to 5e-34 in t and 4e-35 in u for k ≤ 13.

| k | ζ_k | λ(ζ_k) |
|---|---|---|
| 0 | 4.071496844298139347601 | 3.321992118339823988416 |
| 1 | 37.52679873931686065435 | 1.664156189756795221863 |
| 2 | 428.9125290822092728221 | 2.108541102106430075023 |
| 3 | 4532.148619116816063372 | 1.967465558668592682653 |
| 4 | 48978.39310970605031819 | 2.009976404966977661097 |
| 5 | 525619.5981255673089760 | 1.996962036282534254649 |
| 6 | 5652734.129545340447792 | 2.000927069125056805562 |
| 7 | 60752545.53471456455653 | 1.999717277313230817741 |
| 8 | 653064520.1915645593962 | 2.000086237250231804973 |
| 9 | 7019748614.451326094846 | 1.999973697138317437130 |
| 10 | 75456212540.60467720589 | 2.000008022672705959444 |
| 11 | 811084334018.9595955181 | 1.999997553007055725467 |
| 12 | 8718419574484.085357528 | 2.000000746357842974979 |
| 13 | 93715039353035.11433632 | 1.999999772353352756700 |

exp(2π/√7) = 10.749087029163505, −exp(−π/√7) = −0.305010092815543.

| k | r_k | q_k |
|---|---|---|
| 0 | 9.21695 | −0.25404 |
| 1 | 11.42950 | −0.32319 |
| 2 | 10.56660 | −0.29974 |
| 3 | 10.80688 | −0.30664 |
| 4 | 10.73166 | −0.30451 |
| 5 | 10.75442 | −0.30516 |
| 6 | 10.747462049767588 | −0.304963976393733 |
| 7 | 10.749582827247913 | −0.305024160661751 |
| 8 | 10.748935820908187 | −0.305005802154649 |
| 9 | 10.749133150618164 | −0.305011401526624 |
| 10 | 10.749072961785578 | −0.305009693646962 |
| 11 | 10.749091319867962 | −0.305010214566129 |
| 12 | 10.749085720456477 | −0.305010055680398 |

Deviations from each limit shrink by about 0.305 per step and alternate. For k ≥ 6 the true margins are about 0.447 / 0.451 for r and 0.0250 / 0.0250 for q. k = 0, 1 fall outside both intervals. ζ6 ≈ 5.65e6 ≥ 300000.

## 3. Route (by hand)
- ε_k ≤ √Nw(ζ6) = √8·x6 ≤ √8·0.00049 = 0.0013859293 for every k ≥ 6 (Nw non-increasing); all four segment bounds weaken as ε grows; 16ε ≤ 0.0221749, 36ε ≤ 0.0498935.
- L ∈ [2.3356689, 2.4153077], r ∈ [10.336371, 11.193214] (margins 0.0364, 0.0068).
- q = −exp(D/2) ∈ [−0.3297016, −0.2814198] (margins 0.000298, 0.00142).
- Largest upper bound on λ(ζ6) for which each stated bound still follows: q ≥ −0.33: 2.0009916; r ≤ 11.2: 2.0009944; q ≤ −0.28: 2.0010405; r ≥ 10.3: 2.0010698. The bound used is 2.000980.
- The limit conjunct follows from the first two segment bounds (ε_k → 0). No gaps; the Lean proof needs about five digits for exp and π.

## 4. Prior art (from memory, not looked up)
- The ratio exp(2π/√7) ≈ 10.75 is classical (linearisation eigenvalues (−1 ± i√7)/2; Chandrasekhar 1939 Ch. IV; Bonnor–Ebert stability literature, e.g. Chavanis 2002; Joseph–Lundgren 1973).
- Explicit two-sided bounds from a named turning point on: none known to the referee, published or formally verified.

## Corrections
None required.
