# Blind restatement brief (run 2026-11-15T1828Z)

You are formalizing one claim in Lean 4 + Mathlib. Do NOT read anything in the repository /home/claude/formalization (no `Checked/`, `Work/`, `runs/` other than your own output folder, no `*.md` files, no git history). Write your output only to `runs/2026-11-15T1828Z/blind/`. Do not compile; write carefully against current Mathlib names (`EuclideanSpace`, `Metric.ball`, `Metric.closedBall`, `ContDiffOn`, `ContinuousOn`, `InnerProductSpace.laplacian` (notation `Δ` under `open InnerProductSpace Laplacian`), `Real.exp`, `Function.Injective`, `Set.Infinite`).

The claim (mathematics / combustion theory: the Gelfand–Bratu problem in the unit ball of ℝ³):

> Consider the Dirichlet problem Δu + λ e^u = 0 in the open unit ball B of ℝ³, u = 0 on the unit sphere, for a real parameter λ. A radial classical solution is a function u that is twice continuously differentiable in the open ball, continuous on the closed ball, zero on the unit sphere, depends only on |x| on the closed ball, and satisfies the equation at every point of the open ball (Δ the usual Laplacian).
> Claim: (i) for λ = 2 the problem has infinitely many distinct radial classical solutions; (ii) for every natural number N there is ε > 0 such that for every λ with |λ − 2| < ε the problem has at least N distinct radial classical solutions; (iii) for every λ with 2 ≤ λ < 3.321992118 it has at least two distinct radial classical solutions.

Write `runs/2026-11-15T1828Z/blind/GelfandPDEManyBlind.lean` (`import Mathlib`, any definitions you need, one theorem `blind_gelfand_pde_many` stating the claim as faithfully as you can, `:= by sorry`) and a short `notes.md` listing every interpretive choice (solution class, how "infinitely many" and "at least N distinct" are stated). If your Write tool is refused, put both file contents in your final message. Always report both file contents in your final message.
