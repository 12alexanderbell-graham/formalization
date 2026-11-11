# Interpretive choices
- Solutions are functions f : ℝ → ℝ, only the values on [0,∞) matter; derivatives are `derivWithin _ (Ici 0)` (one-sided at 0), nested for f', f'', f'''.
- Regularity: `ContDiffOn ℝ 3 f (Ici 0)` (so f''' exists and the ODE is meaningful); this is an added assumption, not stated in the claim.
- ODE imposed for all η ≥ 0 (including the boundary).
- f(0)=0, f'(0)=0, f'→1 via `Tendsto ... atTop (𝓝 1)`.
- Separation profile: f''(0)=0, f''(η)>0 for η>0, and for every real M, eventually (atTop) M*(1-f') ≤ f''.
- β real (no sign restriction); the two profiles f₁, f₂ may be different functions.
- Packaged as a def `IsSepProfile`; the theorem has the conclusion β₁ = β₂, proof `sorry`.
