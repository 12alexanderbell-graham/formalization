# Blind restatement brief (run 2026-11-12T0427Z)

You are formalizing one claim in Lean 4 + Mathlib. Do NOT read anything in the repository /home/claude/formalization (no `Checked/`, `Work/`, `runs/` other than your own output folder, no `*.md` files, no git history). Write your output only to `runs/2026-11-12T0427Z/blind/`. Do not compile (a long build is using the machine's memory); write carefully against current Mathlib names (`HasDerivWithinAt`, `HasDerivAt`, `deriv`, `derivWithin`, `ContDiffOn`, `StrictMonoOn`, `StrictAntiOn`, `Set.Icc`, `Real.exp`, `Real.sqrt`, `Real.pi`).

The claim (astrophysics: the Bonnor–Ebert sphere, a pressure-confined self-gravitating isothermal gas sphere):

> Let ψ be the regular solution of the isothermal Lane–Emden (Emden–Chandrasekhar) equation (1/ξ²) d/dξ (ξ² dψ/dξ) = e^{−ψ} with ψ(0) = 0 and ψ'(0) = 0, so that the density is ρ = ρ_c e^{−ψ}. A sphere truncated at dimensionless radius ξ and confined by an external pressure has dimensionless mass m(ξ) = (4π)^{−1/2} e^{−ψ(ξ)/2} ξ² ψ'(ξ) (mass in units of c_s⁴ G^{−3/2} P_ext^{−1/2}) and centre-to-edge density contrast ρ_c/ρ(ξ) = e^{ψ(ξ)}.
> Claim: there is a radius ξ₁ with 6.4507514 ≤ ξ₁ ≤ 6.4507515 such that m is strictly increasing on [0, ξ₁] and strictly decreasing on [ξ₁, 7]; at ξ₁ the mass satisfies 1.1822265 ≤ m(ξ₁) ≤ 1.1822266 and the density contrast satisfies 14.042032 ≤ e^{ψ(ξ₁)} ≤ 14.042033.

Write `runs/2026-11-12T0427Z/blind/BonnorEbertBlind.lean` (`import Mathlib`, any definitions you need, one theorem `blind_bonnor_ebert` stating the claim as faithfully as you can for every such solution ψ, `:= by sorry`) and a short `notes.md` listing every interpretive choice (how you state the solution and its regularity at ξ = 0, the domain of the solution, what you assume vs conclude). If your Write tool is refused, put both file contents in your final message. Report the file contents in your final message.
