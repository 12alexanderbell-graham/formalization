# Blind restatement brief (run 2026-11-13T2228Z)

You are formalizing one claim in Lean 4 + Mathlib. Do NOT read anything in the repository /home/claude/formalization (no `Checked/`, `Work/`, `runs/` other than your own output folder, no `*.md` files, no git history). Write your output only to `runs/2026-11-13T2228Z/blind/`. Do not compile (a long build is using the machine's memory); write carefully against current Mathlib names (`HasDerivWithinAt`, `HasDerivAt`, `deriv`, `ContDiffOn`, `IsMaxOn`, `Set.Icc`, `Set.Ici`, `Real.exp`, `Real.sqrt`, `Real.pi`).

The claim (astrophysics: the Bonnor–Ebert sphere, a pressure-confined self-gravitating isothermal gas sphere):

> Let ψ be the regular solution of the isothermal Lane–Emden (Emden–Chandrasekhar) equation (1/ξ²) d/dξ (ξ² dψ/dξ) = e^{−ψ} with ψ(0) = 0 and ψ'(0) = 0, so that the density is ρ = ρ_c e^{−ψ}. A sphere truncated at dimensionless radius ξ and confined by an external pressure has dimensionless mass m(ξ) = (4π)^{−1/2} e^{−ψ(ξ)/2} ξ² ψ'(ξ).
> Claim: the mass has a strict global maximum over all radii ξ ≥ 0: there is a radius ξ₁ with 6.4507514 ≤ ξ₁ ≤ 6.4507515 such that m(ξ) < m(ξ₁) for every radius ξ ≥ 0 other than ξ₁, and 1.1822265 ≤ m(ξ₁) ≤ 1.1822266.

Write `runs/2026-11-13T2228Z/blind/BonnorEbertGlobalBlind.lean` (`import Mathlib`, any definitions you need, one theorem `blind_bonnor_ebert_global` stating the claim as faithfully as you can for every such solution ψ, `:= by sorry`) and a short `notes.md` listing every interpretive choice (how you state the solution and its regularity at ξ = 0, its domain, what you assume vs conclude). If your Write tool is refused, put both file contents in your final message. Always report both file contents in your final message.
