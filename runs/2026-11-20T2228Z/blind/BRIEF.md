# Blind restatement brief (run 2026-11-20T2228Z)

You are formalizing one claim in Lean 4 + Mathlib. Do NOT read anything in the repository /home/claude/formalization (no `Checked/`, `Work/`, `runs/` other than your own output folder, no `*.md` files, no git history). Write your output only to `runs/2026-11-20T2228Z/blind/`. Do not compile; write carefully against current Mathlib names (`EuclideanSpace`, `Metric.ball`, `Metric.closedBall`, `Metric.sphere`, `ContDiffOn`, `ContinuousOn`, `InnerProductSpace.Laplacian` notation `Δ`, `Real.exp`).

The claim (mathematics / combustion theory: the Gelfand–Bratu problem in the unit ball of ℝ³; Joseph and Lundgren 1973 give the critical parameter of the ball):

> Consider the boundary-value problem Δu + λ e^u = 0 in the open unit ball B of ℝ³, u = 0 on the unit sphere, where Δ is the Laplacian. A classical solution is a function that is twice continuously differentiable in B, continuous on the closed ball, satisfies the equation at every point of B and vanishes on the sphere. No symmetry of the solution is assumed.
> Claim: if the problem has a classical solution for the real parameter λ, then λ ≤ 3.321992119 (the critical parameter λ* of the ball is about 3.32199).

Write `runs/2026-11-20T2228Z/blind/GelfandPDEBoundBlind.lean` (`import Mathlib`, any definitions you need, one theorem `blind_gelfand_pde_bound` stating the claim as faithfully as you can, `:= by sorry`) and a short `notes.md` listing every interpretive choice (the solution class, the domain of u, how the boundary condition and the equation are stated, the sign convention, whether λ ranges over all reals). If your Write tool is refused, put both file contents in your final message. Always report both file contents in your final message.
