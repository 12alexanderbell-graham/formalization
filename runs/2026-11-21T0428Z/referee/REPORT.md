VERDICT: STANDS (Opus referee, run 2026-11-21T0428Z; its Write was refused by the harness, so this file is the report relayed verbatim in substance by the run; scripts in `scripts/`).

## 1. Attack on the statement
- Hypotheses not vacuous and pin W: continuity of φ at 0 with (s²φ)′ = −s²e^w forces φ(0) = 0; the singular branch is excluded; values for s < 0 never enter.
- ζ is uniquely pinned: ζ0 is the unique global maximiser; the `2k` conjunct makes ζ(2k+1) the unique minimiser on [ζ(2k), ∞); the `2k+1` conjunct makes ζ(2k+2) the unique maximiser on [ζ(2k+1), ∞); by induction any two witnesses agree. ζ 3 is the 4th turning point, ζ 4 the 5th.
- Decimal literals exact rationals via OfScientific (`1.967510` = 1.96751). No junk values (2/s only under s > 0). Docstring matches every clause.

## 2. Independent computation (mpmath Taylor method in s, three runs dps 50/50/60, orders 40/50/60; cross-check: homology system in log s with scipy DOP853, agreement 12-13 digits)
| n | ζ_n | λ(ζ_n) |
|---|---|---|
| 0 | 4.0714968442981393476012090333447161 | 3.3219921183398239884164780820029956 |
| 1 | 37.526798739316860654350843223698109 | 1.6641561897567952218629967431777206 |
| 2 | 428.91252908220927282213410666211415 | 2.1085411021064300750234186925577264 |
| 3 | 4532.1486191168160633720693854051078 | 1.9674655586685926826532908322129224 |
| 4 | 48978.393109706050318185146671749763 | 2.0099764049669776610976733828799578 |
| 5 | 525619.59812556730897597816734197902 | 1.9969620362825342546493531814727079 |
| 6 | 5652734.1295453404477920104400682202 | 2.0009270691250568055615090264955324 |

λ₃ ∈ [1.967422, 1.967510]: margins 4.356e-5 / 4.444e-5. λ₄ ∈ [2.009926, 2.010028]: margins 5.041e-5 / 5.160e-5. The statement would still be true with bands one tenth as wide (λ₃ falls out only at about one hundredth).

## 3. Route
λ = uv, λ′ = λ(2 − v)/s, λ = 2u at v = 2: correct. Gap to close: a zero of v − 2 in the fifth bracket is identified with ζ₄ only if v < 2 is certified on the whole stretch from the fourth bracket (already identified with ζ₃) to the fifth (or ζ₅ is bounded below); the same for ζ₃. A condition on the proof, not a defect of the statement.

## 4. Prior art (from memory, low confidence; no search)
λ* ≈ 3.32 classical; λ at the 4th and 5th turning points (≈ 1.96747, ≈ 2.00998) not known to be printed anywhere.

## Corrections
None required.
