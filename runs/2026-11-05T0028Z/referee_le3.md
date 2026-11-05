# Referee report: `Work.Math.LaneEmden.laneEmden3_constants`

**Verdict: STANDS.** The statement is true and not vacuous. The intervals contain the values with comfortable margins. The conventions are the standard ones. The certified enclosure appears to be new; the digits themselves are not.

## 1. Independent computation (40 digits, two methods agree to 1e-40)
- Method A: a power series at 0 (θ = Σ a_k ξ^{2k}, 80 terms, tail about 1e-113 at ξ = 0.5), then mpmath `odefun` (Taylor method), then `findroot`.
- Method B: my own Taylor stepper for ξθ'' + 2θ' + ξθ³ = 0. It starts at 0.25 and uses steps of h = 0.05 with 42 terms per step.
- Sanity check: scipy DOP853, which agrees to about 1e-13.

| quantity | value | margin to lower | margin to upper |
|---|---|---|---|
| ξ₁ | 6.896848619376960375 | 4.38e-9 | 5.62e-9 |
| ω₃ = −ξ₁²θ'(ξ₁) | 2.018235950966228403 | 5.97e-9 | 4.03e-9 |
| ξ₁³/(3ω₃) | 54.18248110734076302 | 6.07e-7 | 3.93e-7 |

All three values lie well inside their intervals, at roughly 40–60% of the half-width.

## 2. Hypotheses
- **θ'(0) = 0 follows from the hypotheses.**
  - hθ makes θ continuous on [0,7].
  - hφ makes φ continuous on (0,7], and hφ0 extends this to [0,7].
  - On (0,7), (ξ²φ)' = −ξ²θ³. Integrate from ε to ξ and let ε → 0. Since φ is bounded, ε²φ(ε) → 0, so ξ²φ(ξ) = −∫₀^ξ s²θ³.
  - Hence φ(ξ) = −ξ/3 + o(ξ), so φ(0) = 0 by continuity.
- **The solution is unique.** Integrating once more gives the Volterra equation θ(ξ) = 1 − ∫₀^ξ s(1 − s/ξ)θ(s)³ ds, whose kernel lies in [0, ξ]. Two continuous solutions are bounded on [0,7], the cubic is Lipschitz on bounded sets, and Gronwall's inequality makes them equal. So every (θ, φ) satisfying the hypotheses is the Lane–Emden function on [0,7].
  - The singular branch θ ~ A + B/ξ is excluded because θ is continuous at 0.
  - hφ0 is in fact redundant. If C = lim ε²φ(ε) were nonzero, then φ ~ C/ξ² would not be integrable, which contradicts θ being continuous at 0. Redundancy is harmless.
- **Junk values and conventions are fine.**
  - 2/ξ at ξ = 0 is never evaluated, because hφ is stated on Ioc.
  - HasDerivWithinAt on Icc is one-sided only at 0 and 7. ξ₁ is interior.
  - The values of θ and φ outside [0,7] are irrelevant.
  - The division in the last conjunct is safe, because ω₃ is bounded away from 0.
  - Parsing is correct: `θ ξ ^ 3` = (θ ξ)³.
- **The statement is not vacuous.** A solution exists on all of [0,∞):
  - near 0, by the Volterra fixed point (an analytic series);
  - beyond that, because the energy φ²/2 + θ⁴/4 has derivative −2φ²/ξ ≤ 0, so the solution cannot blow up.
- **Nothing is trivially true.** The ∃ requires the real zero, and the condition "0 < θ on [0, ξ₁)" pins down the first zero.
- **Suggestion (not a correction):** the theorem is universally quantified, so its content depends on existence. The existence statement promised in the docstring should be stated and proved as a companion.

## 3. Conventions
- ω₃ = −ξ₁²θ'(ξ₁) is the standard definition, as is ρ_c/ρ̄ = ξ₁³/(3ω₃). This follows from M = 4πa³ρ_c ω and R = aξ₁.
- ω₃ is the Chandrasekhar-mass factor: M_Ch = ω₃(√(3π)/2)(ħc/G)^{3/2}/(μ_e m_H)², with ω₃ = 2.01824. This matches the computed 2.0182359…
- Chandrasekhar (1939), Table 4, prints 6.89685, 2.01824 and 54.1825. I am quoting this from memory; I did not re-verify it online.
- Horedt (1986) gives ξ₁ = 6.89684862, as cited in [arXiv:1608.06756](https://arxiv.org/pdf/1608.06756), Table 1. Caimmi (1983) gives the same value.
- All printed values agree with my computation after rounding.

## 4. Prior art
I searched arXiv and the general web. I found no rigorous, interval or computer-assisted enclosure of the radial Lane–Emden ODE constants or zeros. The hits on "rigorous Lane–Emden" all concern the PDE −Δu = |u|^{p−1}u on bounded domains:
- Tanaka–Plum–Sekine–Kashiwagi–Oishi, [arXiv:1607.04619](https://arxiv.org/abs/1607.04619)
- [arXiv:2102.07596](https://arxiv.org/abs/2102.07596), on symmetries of nodal solutions on squares
- [arXiv:1601.01543](https://arxiv.org/html/1601.01543v1), on Emden's equation on an L-shaped domain

The other hits are floating-point or analytic approximations: [astro-ph/0107395](https://arxiv.org/pdf/astro-ph/0107395), [astro-ph/0402130](https://arxiv.org/pdf/astro-ph/0402130), [arXiv:1611.07202](https://arxiv.org/abs/1611.07202) and [arXiv:2507.03961](https://arxiv.org/html/2507.03961v1).

- **The numbers are not new.** Floating-point values are known to ≥ 10 digits (Horedt; Boyd 2011).
- **The certification probably is new.** I found no certified enclosure, so a formally certified one would be new as far as this screen goes. The caveat is that validated-ODE tools (CAPD, VNODE) make such a computation routine, and an unindexed thesis or report may exist.

Computation scripts are in a temp dir outside the repo (/tmp/tmp.SYtCYoeMRd).
