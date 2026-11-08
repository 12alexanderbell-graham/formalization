# Encoding choices
- Solution = f : ℝ → ℝ (values off [0,∞) irrelevant); no assumption outside [0,∞).
- Derivatives: iterated `derivWithin (Ici 0)`; f', f'', f''' defined this way (one-sided at 0).
- Regularity: f, f', f'' DifferentiableWithinAt (Ici 0) at every x ≥ 0 (so f''' exists everywhere on [0,∞)).
- ODE f''' + f f'' + β(1 - f'^2) = 0 imposed for all η ≥ 0, β a parameter (1/2 and 0).
- BCs: f 0 = 0, f' 0 = 0 (derivWithin), Tendsto f' atTop (𝓝 1).
- Claim A: ∃ solution with 0.927680039 < f''(0) < 0.927680040 (strict).
- Claim B: ∀ solutions, 0.4695999883610 ≤ f''(0) ≤ 0.4695999883611 (inclusive); no existence asserted (vacuous if none).
- Decimals as real literals; f''(0) = derivWithin (derivWithin f (Ici 0)) (Ici 0) 0.
