VERDICT: STANDS. The last conjunct says what the docstring says, the numbers are right with wide margins, and the planned route works with small but positive worst-case margins and no gap.

(Referee: Opus subagent, ≈ 3 min. Its own write of this file was refused by the subagent harness; the text below is its final message, saved verbatim by the run.)

# Referee report, run 2026-11-25T2228Z: BonnorEbertTurningBounds

I read only runs/2026-11-25T2228Z/lean/BonnorEbertTurningBounds.lean and the BRIEF. I did not run Lean. My scripts are:
- runs/2026-11-25T2228Z/referee/scripts/extrema.py (numerics)
- runs/2026-11-25T2228Z/referee/scripts/margins.py (route margins in interval arithmetic)

## 1. Attack on the statement
- **Index convention:** the conjunct is `∀ k, 5 ≤ k → …` on `ξ (k+1) / ξ k`. Its first instance is ξ₆/ξ₅, which matches the docstring and the brief. In 0-indexing ξ₅ is the "sixth extremum" of the module doc.
- **Intervals:** both are closed (`≤` on each side): 9.2 ≤ R ≤ 12.9 and −0.42 ≤ D ≤ −0.21. `-0.42` is −(0.42) in ℝ.
- **Deviation quotient:** the numerator is m(ξ(k+1)) − √(2/π) and the denominator is m(ξ k) − √(2/π). m is spelled s²(−φ)e^{w/2}/√(4π), exactly as in the other conjuncts and in the limit conjunct. This is consistent with 4πm² = uv³.
- **Junk values:** none. ξ k ≥ ξ 0 ≥ 6.45 > 0 because ξ is StrictMono. The deviation denominators are nonzero because of the alternation conjunct m(ξ(2k+1)) < √(2/π) < m(ξ(2k)).
- **Vacuity:** none.
  - The hypotheses hold for the regular isothermal solution. φ(0) = 0 is not assumed, but it is forced: s²φ = C − ∫₀ˢ t²e^w, and continuity of φ at 0 gives C = 0.
  - The bounds are proper constraints: the true values are ≈10.749 and ≈−0.305.
  - Under the hypotheses, ξ is forced to be the ordered list of zeros of g, so ξ cannot be chosen cheaply.

## 2. Numbers (independent computation)
**Method:**
- I integrated the homology system u' = u(3−u−v), v' = v(u−1) in t = log s with mpmath odefun (Taylor method).
- Initial data come from the w-series (−1/6, 1/120, −1/1890, 61/1632960, −629/224532000, derived with sympy).
- Zeros of g were found by a scan followed by findroot.
- I computed m = √(uv³/4π) and cross-checked it against √(2/π)u² at the zeros; they agree to 1e−41.

**Error estimate:** I ran it twice, at dps 40 with s₀ = 1e−4 and at dps 30 with s₀ = 1e−5. The relative difference in ξ_k is ≤ 1.3e−30, in m it is ≤ 2e−31, and in the quotients it is ≤ 1e−25 (k ≤ 13).

| k | ξ_k | m(ξ_k) − √(2/π) |
|---|---|---|
| 0 | 6.4507514441740737 | +0.38434203 |
| 1 | 67.007548719595240 | −0.10351804 |
| 2 | 733.76924368659781 | +0.032805497 |
| 3 | 7849.6320485004269 | −0.0098903729 |
| 4 | 84506.328975744926 | +0.0030273893 |
| 5 | 907946.19315370932 | −9.2238556e−4 |
| 6 | 9760974.9810400212 | +2.8142979e−4 |
| 7 | 1.049170438187439e8 | −8.5830285e−5 |
| 8 | 1.127777279202882e9 | +2.6179907e−5 |
| 9 | 1.212252746161294e10 | −7.9850611e−6 |
| 10 | 1.303062622470802e11 | +2.4355312e−6 |
| 11 | 1.400672830251776e12 | −7.4286095e−7 |
| 12 | 1.505595586675034e13 | +2.2658015e−7 |

**Checks against the brief:**
- ξ₀ lies in [6.4507514, 6.4507515].
- ξ₄ = 84506.33 lies in [84497, 84516] and is below 300000.
- ξ₅ = 907946 is above 300000.
- Nw(300000) = 3.23132e−5, which is ≤ 3234e−8.

| k | R = ξ_{k+1}/ξ_k | R−9.2 | 12.9−R | D | D+0.42 | −0.21−D |
|---|---|---|---|---|---|---|
| 4 | 10.74412064 | 1.544 | 2.156 | −0.3046801981 | 0.1153 | 0.0947 |
| 5 | 10.75060951 | 1.551 | 2.149 | −0.3051107954 | 0.1149 | 0.0951 |
| 6 | 10.74862337 | 1.549 | 2.151 | −0.3049793851 | 0.1150 | 0.0950 |
| 7 | 10.74922852 | 1.549 | 2.151 | −0.3050194597 | 0.1150 | 0.0950 |
| 8 | 10.74904388 | 1.549 | 2.151 | −0.3050072359 | 0.1150 | 0.0950 |
| 9 | 10.74910019 | 1.549 | 2.151 | −0.3050109642 | 0.1150 | 0.0950 |
| 10 | 10.74908301 | 1.549 | 2.151 | −0.3050098270 | 0.1150 | 0.0950 |
| 11 | 10.74908825 | 1.549 | 2.151 | −0.3050101739 | 0.1150 | 0.0950 |

The limits are e^{2π/√7} = 10.74908703 and −e^{−π/√7} = −0.3050100928, which matches the docstring.

## 3. Route (by hand)
**(a) Uniqueness.** By induction:
- ξ₀ is the unique strict maximiser on [0,∞).
- Given ξ_{2k}, ξ_{2k+1} is the unique strict minimiser on [ξ_{2k},∞), and similarly for ξ_{2k+2}.

So the frozen ξ equals the program's sequence, and ξ₅ is the first tail zero (> 300000).

**(b) g = 0 at each ξ_k.**
- For k ≥ 1, ξ_k is interior (ξ_{k−1} < ξ_k), so it is a two-sided local extremum.
- HasDerivWithinAt on Ici 0 at s > 0 is a full derivative, so m'(ξ_k) = 0.
- Directly: (s²(−φ)e^{w/2})' = s²e^{w/2}(e^w − φ²/2), and 2u − v = (s/(−φ))(2e^w − φ²).
- So m' = 0 ⇔ g = 0, using φ < 0 for s > 0 (from s²φ = −∫t²e^w). This agrees with s(uv³)' = uv³g.

**Step the route leaves implicit: consecutive extrema are consecutive zeros of g.** The segment bounds need this, and it does hold:
- At a zero of g (v = 2u), dg/dt = 8u(1−u). This is ≠ 0, because u = 1 would put the trajectory on the equilibrium (1,2), which ODE uniqueness rules out.
- So zeros of g are simple, and m changes monotonicity at each one.
- A zero strictly between ξ_k and ξ_{k+1} would therefore contradict the StrictAnti/StrictMono conjunct on [ξ_k, ξ_{k+1}].

**(c) Constants.**
- **ε:** ξ_k ≥ ξ₅ > 300000 and Nw is non-increasing, so ε = √Nw(ξ_k) ≤ √3234e−8 = 0.00568683 ≤ 0.0057 (slack 1.3e−5).
- **|x|:** Nw = 32x² at zeros, so |x| ≤ √(3234e−8/32) = 0.00100530 ≤ 1/990 = 0.00101010.
- **Sign:** m − √(2/π) = √(2/π)(u²−1) has the sign of x, and the alternation conjunct gives x_{k+1}/x_k = −exp(ΔlogNw/2).
- **D:** D = (u_{k+1}²−1)/(u_k²−1) = (x_{k+1}/x_k)(2+x_{k+1})/(2+x_k). This is correct.
- All four bounds are monotone in ε, so ε = 0.0057 is the worst case.

Worst case with π ∈ [3.141592, 3.141593] and √7 ∈ [2.64575, 2.6458] (I checked that this interval brackets 7 when squared), in outward-rounded interval arithmetic:

| Bound | Worst-case value | Margin | Largest ε that still works |
|---|---|---|---|
| L | ∈ [2.2216194, 2.5506672] | – | – |
| e^L ≥ | 9.2222533 | +0.02225 | 0.005796 |
| e^L ≤ | 12.8156513 | +0.08435 | 0.005897 |
| D ≥ −e^{−(1−36ε)L_min/2}·(2+1/990)/(2−1/990) | −0.41401153 | +0.00599 | 0.005988 |
| D ≤ −e^{−(1+36ε)L_max/2}·(2−1/990)/(2+1/990) | −0.21480124 | +0.00480 | 0.006042 |

All four inequalities hold, so there is no gap. The tightest is R ≥ 9.2: it needs ε ≤ 0.005796, the brief allows 0.0057, and the true value is 0.005687. That is about 1.7% headroom in ε, which is tight but sound. The formal exp bounds need roughly 2e−3 relative accuracy near e^{2.22} and e^{2.55}, and roughly 1e−2 for e^{−0.88} and e^{−1.54}.

## 4. Prior art (from memory; I did no web lookup)
The asymptotic results are classical: ratio → e^{2π/√7} ≈ 10.75, deviation ratio → −e^{−π/√7}, and a spiral about the singular solution (1,2) in homology variables. Sources are Chandrasekhar 1939, Ebert 1955, Bonnor 1956, Lynden-Bell & Wood 1968 and Chavanis 2002. I know of no published explicit, non-asymptotic, all-k bounds of this kind, and no formal verification in any proof assistant. Read this as "not known to the referee", not as the result of a literature search.

## Corrections
None required. One optional addition: the module doc could name the "consecutive extrema are consecutive zeros of g" step and its justification (g' = 8u(1−u) ≠ 0 at zeros, plus strict monotonicity between extrema), since the formal proof has to discharge it.
