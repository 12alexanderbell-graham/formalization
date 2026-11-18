# Blind restatement brief (run 2026-11-18T0428Z)

You are formalizing one claim in Lean 4 + Mathlib. Do NOT read anything in the repository /home/claude/formalization (no `Checked/`, `Work/`, `runs/` other than your own output folder, no `*.md` files, no git history). Write your output only to `runs/2026-11-18T0428Z/blind/`. Do not compile; write carefully against current Mathlib names (`EuclideanSpace`, `Metric.ball`, `Metric.closedBall`, `ContDiffOn`, `ContinuousOn`, `InnerProductSpace.laplacian` (notation `Δ` under `open InnerProductSpace Laplacian`), `Real.exp`).

The claim (mathematics / combustion theory: the Gelfand–Bratu problem in the unit ball of ℝ³):

> Consider the Dirichlet problem Δu + λ e^u = 0 in the open unit ball B of ℝ³, u = 0 on the unit sphere, for a real parameter λ. A radial classical solution is a function u that is twice continuously differentiable in the open ball, continuous on the closed ball, zero on the unit sphere, depends only on |x| on the closed ball, and satisfies the equation at every point of the open ball (Δ the usual Laplacian). Two solutions count as the same if they agree on the closed ball.
> Claim (exact counts): there are numbers λ*, λ₁, λ₂ with 3.321992118 ≤ λ* ≤ 3.321992119 and 0 < λ₁ < 2 < λ₂ < λ* such that: (a) for λ > λ* there is no radial classical solution; (b) for λ = λ* there is exactly one; (c) for every λ with λ₂ < λ < λ* there are exactly two; (d) for every λ with 0 < λ < λ₁ there is exactly one.

Write `runs/2026-11-18T0428Z/blind/GelfandPDECountBlind.lean` (`import Mathlib`, any definitions you need, one theorem `blind_gelfand_pde_count` stating the claim as faithfully as you can, `:= by sorry`) and a short `notes.md` listing every interpretive choice (solution class, how "exactly one/two" and "the same" are stated). If your Write tool is refused, put both file contents in your final message. Always report both file contents in your final message.
