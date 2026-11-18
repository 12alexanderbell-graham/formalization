# Blind restatement brief (run 2026-11-18T1628Z)

You are formalizing one claim in Lean 4 + Mathlib. Do NOT read anything in the repository /home/claude/formalization (no `Checked/`, `Work/`, `runs/` other than your own output folder, no `*.md` files, no git history). Write your output only to `runs/2026-11-18T1628Z/blind/`. Do not compile; write carefully against current Mathlib names (`HasDerivWithinAt`, `ContinuousWithinAt`, `Set.Ici`, `Set.encard`, `Filter.Tendsto`, `Real.exp`, `Real.sqrt`, `Real.pi`, `StrictMono`).

The claim (astrophysics: pressure-confined isothermal gas spheres, Bonnor 1956 / Ebert 1955):

> The isothermal Lane–Emden (Emden–Chandrasekhar) equation in the variable w = −ψ is w'' + (2/s) w' + e^w = 0 for s > 0, with the regular centre w(0) = 0, w'(0) = 0. Take any function w on the half-line s ≥ 0 that is differentiable on [0, ∞) (one-sided at 0) with derivative φ, where φ is continuous at 0 and, for s > 0, differentiable with φ'(s) = −(2/s) φ(s) − e^{w(s)}, and w(0) = 0. The dimensionless mass of the sphere cut at radius s (the mass of a sphere of given temperature in equilibrium with a given external pressure) is m(s) = s² (−φ(s)) e^{w(s)/2} / √(4π).
> For a number μ, let N(μ) be the number of radii s ≥ 0 with m(s) = μ (the number of equilibrium spheres of dimensionless mass μ).
> Claim (exact counts): there is a strictly increasing sequence of radii ξ₀ < ξ₁ < ξ₂ < … tending to infinity, with 6.4507514 ≤ ξ₀ ≤ 6.4507515, whose mass values m_k = m(ξ_k) satisfy 1.1822265 ≤ m₀ ≤ 1.1822266, 0.694366 ≤ m₁ ≤ 0.694367, 0.8306 ≤ m₂ ≤ 0.8308, 0.787992 ≤ m₃ ≤ 0.787995, 0.80091 ≤ m₄ ≤ 0.800916, and m_k → √(2/π) as k → ∞, such that:
> (a) N(μ) = 0 for every μ > m₀; (b) N(m₀) = 1;
> (c) for every k ≥ 0 and every μ with m_{2k+2} < μ < m_{2k}: N(μ) = 2k + 2; (d) for every k ≥ 0: N(m_{2k+2}) = 2k + 3;
> (e) for every μ with 0 < μ < m₁: N(μ) = 1; (f) for every k ≥ 0: N(m_{2k+1}) = 2k + 2;
> (g) for every k ≥ 0 and every μ with m_{2k+1} < μ < m_{2k+3}: N(μ) = 2k + 3;
> (h) N(√(2/π)) is infinite.

Write `runs/2026-11-18T1628Z/blind/BonnorEbertCountBlind.lean` (`import Mathlib`, any definitions you need, one theorem `blind_bonnor_ebert_count` stating the claim as faithfully as you can, `:= by sorry`) and a short `notes.md` listing every interpretive choice (the solution class, how N is stated, how "infinite" is stated). If your Write tool is refused, put both file contents in your final message. Always report both file contents in your final message.
