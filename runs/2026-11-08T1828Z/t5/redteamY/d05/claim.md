Category: misleading-record
Reader would wrongly believe: `decel a t` is undefined where a'(t)=0, so no headline asserts anything there
Why it is false: In Lean decel a t = -(a''a)/a'^2 is the junk value 0 whenever deriv a t = 0 (x/0 = 0), so theorems about decel DO assert equations there (round W d01 certified decel = 0 at a' = 0). The phrase tells the reader that the junk case is excluded; the printed body shows a division but nothing about its value at zero. No rule compares the phrase with Lean semantics.
Expected: ACCEPTED (P1 passes - no formula character; U2 passes; the junk-value StatementDeps rule only looks at statements, not at the phrase's promise).
Generated line (CLAIMS.md after regeneration): phrase (hand-written, linted): the deceleration parameter of the scale factor `a` at time `t` (not defined where the first derivative of `a` vanishes, and no claim is made there); by definition, `decel a t` is `-(deriv (deriv a) t * a t) / deriv a t ^ 2`
