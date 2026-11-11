# Interpretive choices
- f, f', f'', f''' are separate functions f f1 f2 f3 : ℝ → ℝ linked by HasDerivWithinAt on Ici 0 (one-sided at 0), avoiding iteratedDerivWithin; f1 is f', etc.
- Smoothness is implied by the chain of derivatives up to third order existing on [0, ∞).
- ODE required for all η ≥ 0 (Ici 0), including the wall.
- f(0)=0, f'(0)=0, f'→1 at atTop (nhds 1); wall shear f''(0)=0; f''(η)>0 for η>0 (strict, open half-line).
- Super-exponential condition: ∀ M : ℝ, ∀ᶠ η in atTop, M*(1 - f'(η)) ≤ f''(η), taken literally (M arbitrary real).
- β = (-0.1988376 : ℝ) as a decimal literal, exact rational -1988376/10^7.
- Conclusion is non-existence (¬ ∃ ...); the statement is only about this exact β, no tolerance.
- Values defined outside [0, ∞) are unconstrained.
