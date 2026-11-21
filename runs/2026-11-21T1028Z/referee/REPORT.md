# Referee report (run 2026-11-21T1028Z; Opus subagent; relayed verbatim in substance from its final message, it wrote only its scripts)

**Verdict: STANDS.**

1. **Statement.** The hypotheses force φ(0) = 0 and w the regular solution ((s²φ)' = −s²e^w, φ continuous at 0). The conjuncts pin ζ: every ζ_k is a strict local extremum of λ on (0, ∞) and no interior point of [ζ_k, ζ_{k+1}] is one, so ζ is the ordered set of turning points. ζ 5 is the sixth turning point (a minimum, λ < 2), ζ 6 the seventh (a maximum). Decimal literals elaborate as exact reals. Quantifiers match the docstring.

2. **Independent computation** (`scripts/turning.py DPS ORDER STEP`, `scripts/turning_s03.py`): 160-term centre series at s₀ = 0.5 (tail ≈ 7e-133), own Taylor integrator for u' = u(3 − u − v), v' = v(u − 1) in t = log s to t = 16, Newton on each step's polynomial for v = 2, λ = 2u. Runs at 50 digits / order 30 / step 0.1, 60 / 40 / 0.05 and 70 / 45 / 0.07 (from s₀ = 0.3) agree to ≥ 38 digits.

| k | ζ_k | λ(ζ_k) |
|---|---|---|
| 0 | 4.0714968442981393476012090333447160751 | 3.3219921183398239884164780820029955691 |
| 1 | 37.526798739316860654350843223698108633 | 1.6641561897567952218629967431777205985 |
| 2 | 428.91252908220927282213410666211414522 | 2.1085411021064300750234186925577263521 |
| 3 | 4532.1486191168160633720693854051077958 | 1.9674655586685926826532908322129224407 |
| 4 | 48978.393109706050318185146671749763203 | 2.0099764049669776610976733828799577551 |
| 5 | 525619.59812556730897597816734197901945 | 1.9969620362825342546493531814727079476 |
| 6 | 5652734.1295453404477920104400682201991 | 2.0009270691250568055615090264953943948 |

All seven bands hold. New bands: λ₅ margins 6.104e-5 / 6.096e-5 (half-width 6.1e-5), λ₆ margins 5.407e-5 / 5.293e-5 (half-width 5.35e-5); bands one tenth as wide around the same centres would still hold.

3. **Route.** Sound provided the proof certifies: v − 2 changes sign across each new bracket (v(a₅) > 2 > v(b₅), v(a₆) < 2 < v(b₆)); v > 2 between the bracket of ζ₄ and that of ζ₅ and v < 2 between those of ζ₅ and ζ₆; uniqueness of each zero in its bracket by v' = v(u − 1)/s ≠ 0, i.e. the u-enclosure over the whole bracket excludes 1 (|u − 1| ≈ 1.5e-3 at ζ₅, 4.6e-4 at ζ₆). Global conjuncts come from the checked main theorem.

4. **Prior art** (one search, not conclusive): no printed λ at the sixth or seventh turning points found; the first three turning values appear to 3–5 digits in bifurcation-diagram papers.
