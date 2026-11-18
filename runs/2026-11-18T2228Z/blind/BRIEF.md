# Blind restatement brief (run 2026-11-18T2228Z)

You are formalizing one claim in Lean 4 + Mathlib. Do NOT read anything in the repository /home/claude/formalization (no `Checked/`, `Work/`, `runs/` other than your own output folder, no `*.md` files, no git history). Write your output only to `runs/2026-11-18T2228Z/blind/`. Do not compile; write carefully against current Mathlib names (`EuclideanSpace`, `Metric.ball`, `Metric.closedBall`, `ContDiffOn`, `ContinuousOn`, `InnerProductSpace.Laplacian` notation `Δ`, `Set.encard`, `ℕ∞`, `Filter.Tendsto`, `StrictMono`, `StrictAnti`, `Real.exp`).

The claim (mathematics / combustion theory: the Gelfand–Bratu problem in the unit ball of ℝ³):

> For a real parameter λ, a radial solution is a function u : ℝ³ → ℝ that is twice continuously differentiable on the open unit ball, continuous on the closed unit ball, zero on the unit sphere, radially symmetric on the closed ball (a function of |x| there), and satisfies Δu + λ e^u = 0 on the open unit ball (Δ the Laplacian). Two solutions are counted as the same when they agree on the closed unit ball. Let N(λ) be the number of distinct radial solutions for λ (as functions on the closed unit ball; possibly infinite).
> Claim: there is a sequence of parameters λ₀, λ₁, λ₂, … (the turning values of the solution branch) with 3.321992118 ≤ λ₀ ≤ 3.321992119, 1.664155 ≤ λ₁ ≤ 1.664157, 2.10852 ≤ λ₂ ≤ 2.10858, the even-indexed values λ₀, λ₂, λ₄, … strictly decreasing, the odd-indexed values λ₁, λ₃, … strictly increasing, λ_{2k+1} < 2 < λ_{2k} for every k, and λ_k → 2, such that:
> (a) N(λ) = 0 for every λ > λ₀; (b) N(λ₀) = 1;
> (c) for every k ≥ 0 and every λ with λ_{2k+2} < λ < λ_{2k}: N(λ) = 2k + 2; (d) for every k ≥ 0: N(λ_{2k+2}) = 2k + 3;
> (e) for every λ with 0 < λ < λ₁: N(λ) = 1; (f) for every k ≥ 0: N(λ_{2k+1}) = 2k + 2;
> (g) for every k ≥ 0 and every λ with λ_{2k+1} < λ < λ_{2k+3}: N(λ) = 2k + 3;
> (h) N(2) is infinite.

Write `runs/2026-11-18T2228Z/blind/GelfandPDECountTurningBlind.lean` (`import Mathlib`, any definitions you need, one theorem `blind_gelfand_pde_count_turning` stating the claim as faithfully as you can, `:= by sorry`) and a short `notes.md` listing every interpretive choice (the solution class, how "counted as the same" and N are stated, how "infinite" is stated). If your Write tool is refused, put both file contents in your final message. Always report both file contents in your final message.
