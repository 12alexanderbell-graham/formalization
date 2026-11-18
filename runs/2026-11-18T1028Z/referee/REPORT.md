# Referee report (run 2026-11-18T1028Z; Opus subagent, blind to Checked/Work; copied from its final message, its own write was refused)

**Verdict: STANDS.** Statement faithful and true; the sharpness clauses pin lam1, lam2 to the band ends; both windows contain them. Caution for the route only: lam1's upper margin is 8.1e-7.

## 1. Statement
- Three existentials, windows lamStar [3.321992118, 3.321992119], lam1 [1.664155, 1.664157], lam2 [2.10852, 2.10858], six count clauses (none above lamStar; one at lamStar; two on (lam2, lamStar); one on (0, lam1); two at lam1; three at lam2). Structural check only (parent not shown to the referee).
- Pinning: N(lam) = number of s > 0 with λ(s) = lam (centre values −W(s) distinct). "N = 1 on (0, lam1)" and "N(lam1) = 2" force lam1 = λ(ζ₁); "N = 2 on (lam2, lamStar)" and "N(lam2) = 3" force lam2 = λ(ζ₂).
- Not vacuous (windows contain the true values); decimal literals are exact rationals on ℝ; no junk values.

## 2. Independent computation (scripts/turning.py, scripts/crosscheck_uv.py)
Centre series to 80 terms, own order-30 Taylor integrator, h = 0.2 and 0.1, 40 and 60 digits; agreement 2e-20 on λ.

| | ζ | λ(ζ) | u at ζ |
|---|---|---|---|
| ζ₀ | 4.0714968442981393476 | 3.3219921183398239884 | 1.661 |
| ζ₁ | 37.526798739316860654 | 1.6641561897567952219 | 0.8321 |
| ζ₂ | 428.91252908220927282 | 2.1085411021064300750 | 1.0543 |

Margins: lam1 1.19e-6 (low), 8.10e-7 (high); lam2 2.11e-5, 3.89e-5; lamStar 3.4e-10, 6.6e-10. Cross-check in homology variables (DOP853, t = ln s) agrees to ≈ 1e-12, λ = 2u at each zero.

## 3. Route
Checked by hand: uv = λ; s v' = v(u − 1), s u' = u(3 − u − v); λ' = λ(2 − v)/s, turning points = zeros of v − 2, λ = 2u there; u < 1 at ζ₁, u > 1 at ζ₂. Conditions for the identification: (1) contiguous chain from ζ₀'s enclosure past ζ₂, each cell with a strict sign of v − 2 or one crossing with v strictly monotone; (2) overlaps of positive length when comparing monotonicity; (3) the v > 2 interval must start at or before ζ₀'s enclosure.

## 4. Prior art
Not read (time).

## 5. Verdict
STANDS.
