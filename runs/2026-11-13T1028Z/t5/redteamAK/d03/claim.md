Category: wrong-number (Correct line of F3)
Reader would wrongly believe: F3 Correct: the true z⁵ coefficient of the lookback series is (7/4)q₀⁴ and the printed value is off by (7/4)q₀⁴.
Why it is false: Line: "- **Correct (inverting ...):** (7/4)q₀⁴; ... Printed − true = (7/4)q₀⁴." Lean `correctD4` in F3_D4_LCDM (and `CCS.lookback_fifth_order`) has 7/8 * q^4; printed 7/2, so the difference is 21/8 (certified difference 0.24 at q₀=−0.55 is 21/8 q₀⁴ = 0.2400; with 7/4 it would be 0.1600). Scope/Plain words still say 21/8 and 7/8.
Expected: ACCEPTED (Correct line is free prose; FB6 has no atom for it).
