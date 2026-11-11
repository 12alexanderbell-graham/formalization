# Interpretive choices
- f : ℝ → ℝ, globally `ContDiff ℝ 3` (half-line only via hypotheses for η ≥ 0; avoids derivWithin).
- Derivatives by iterated `deriv`.
- ODE required for all η ≥ 0 (closed half-line).
- f(0)=0, f'(0)=0 exact; f'→1 by `Tendsto ... atTop (nhds 1)`.
- Separation: f''(0)=0; attached: f''(η)>0 for all η>0.
- "sufficiently large": `∀ᶠ η in atTop`; M real, quantified for every M.
- β in open interval, decimal bounds as exact rationals -1988377351/10^10 and -1988377350/10^10.
- One existential over β, then f (existence of a profile for that β).
