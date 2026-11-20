# Blind restatement brief (run 2026-11-20T1028Z)

You are formalizing one claim in Lean 4 + Mathlib. Do NOT read anything in the repository /home/claude/formalization (no `Checked/`, `Work/`, `runs/` other than your own output folder, no `*.md` files, no git history). Write your output only to `runs/2026-11-20T1028Z/blind/`. Do not compile; write carefully against current Mathlib names (`HasDerivWithinAt`, `HasDerivAt`, `deriv`, `StrictMonoOn`, `StrictAntiOn`, `Filter.Tendsto`, `Filter.atTop`, `nhds`, `Real.exp`).

The claim (mathematics / astrophysics: the isothermal sphere, equivalently radial solutions of the Gelfand–Bratu problem in ℝ³):

> Let w be the regular solution of w'' + (2/s) w' + e^w = 0 for s > 0 with w(0) = 0 (w differentiable on [0, ∞) with derivative φ, φ continuous at 0, and φ' = −(2/s)φ − e^w for s > 0; no condition on w'(0) is imposed beyond what these imply). Let λ(s) = s² e^{w(s)}.
> Claim: there is a strictly increasing sequence ζ₀ < ζ₁ < ζ₂ < … of radii tending to infinity such that λ is strictly increasing on [0, ζ₀], strictly decreasing on [ζ_{2k}, ζ_{2k+1}] and strictly increasing on [ζ_{2k+1}, ζ_{2k+2}] for every k ≥ 0 (so the ζ_k are the turning points of λ), λ(s) → 2 as s → ∞, ζ₀ ∈ [4.071496844, 4.071496845], and the values of λ at the first four turning points satisfy
> λ(ζ₀) ∈ [3.321992118, 3.321992119], λ(ζ₁) ∈ [1.664155, 1.664157], λ(ζ₂) ∈ [2.10852, 2.10858], λ(ζ₃) ∈ [1.9637, 1.9707].

Write `runs/2026-11-20T1028Z/blind/GelfandTurningBlind.lean` (`import Mathlib`, any definitions you need, one theorem `blind_gelfand_turning` stating the claim as faithfully as you can for every such w, `:= by sorry`) and a short `notes.md` listing every interpretive choice (solution class, how the turning points are characterised, how the decimals are written). If your Write tool is refused, put both file contents in your final message. Always report both file contents in your final message.
