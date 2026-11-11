# Interpretive choices
- Functions f : ℝ → ℝ; only values on [0,∞) matter. Derivatives are `derivWithin` on `Ici 0` (d1, d2, d3 nested), so one-sided derivative at 0.
- "Solution" = ContDiffOn ℝ 3 f (Ici 0) (C^3 regularity, my choice), ODE holds for all η ≥ 0, f 0 = 0, f' 0 = 0, f' → 1 at atTop.
- β = -0.1988 as a real literal (-0.1988 : ℝ, exact decimal).
- Attached: 0 < f'' η for all η ≥ 0 (including 0).
- Faster-than-exponential: ∀ M : ℝ, ∀ᶠ η in atTop, M*(1 - f' η) ≤ f'' η (non-strict, as stated).
- Window: strict inequalities with exact decimals 0.0052181, 0.0052182.
- Claim 1 quantifies over all such f (vacuity not excluded); Claim 2 is the separate existence statement.
- No compilation done; names written from memory of Mathlib.
