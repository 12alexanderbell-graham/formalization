Category: wrong-statement (Correct line of F9)
Reader would wrongly believe: F9 Correct: the true denominator R has 264q₀ (instead of 246q₀) in its last bracket.
Why it is false: Line: "- **Correct:** R = ... − (3q₀⁴+34q₀³+180q₀²+264q₀+104); correct − printed ...". Lean `correctR` (shown in F9_values, CLAIMS.md `F9_values`) has `3 * q ^ 4 + 34 * q ^ 3 + 180 * q ^ 2 + 246 * q + 104`; printed R has 246q₀ too, so printed−correct has no q₀ term other than 180q₀² and the stated difference formula (which has no 18q₀-type term) contradicts the new line.
Expected: ACCEPTED (Correct-line formulas are not compared to Lean definitions; FB7 disclosed).
