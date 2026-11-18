# Interpretive choices
- Domain: functions `EuclideanSpace ℝ (Fin 3) → ℝ` (total; only values on the closed ball matter, enforced via the "same" quotient).
- Solution class: `ContDiffOn ℝ 2` on open ball; `ContinuousOn` on closed ball; `u x = 0` when `‖x‖ = 1`; radial = `u x = u y` whenever `‖x‖ = ‖y‖` for x,y in the closed ball; PDE `InnerProductSpace.laplacian u x + lam * Real.exp (u x) = 0` for every x in the open ball (called explicitly, not via `Δ` notation).
- "Same solution": identified by agreement on the closed ball, implemented as the set of restrictions of solutions to the subtype `closedBall 0 1`.
- "Exactly n": `Set.encard` of that set equals `n` (so infinite sets are not counted as n; "no solution" is `encard = 0`).
- Decimals written as real literals `(3.321992118 : ℝ)` etc.; ends are non-strict inequalities as in the brief.
- Existential over lamStar, lam1, lam2 with the six clauses (a)-(f); (d) assumes `0 < lam`, (c) is `lam2 < lam < lamStar`, (a) `lamStar < lam`.
- Not compiled; `laplacian` name/signature assumed `InnerProductSpace.laplacian : (E → F) → E → F`.
