# Modelling choices (FSBlind.lean)
- Derivatives: no `deriv`; explicit functions f1=f', f2=f'', f3=f''' : R -> R with `HasDerivWithinAt ... (Ici 0) x` for every x >= 0. This gives one-sided derivatives at 0 and avoids junk-value `deriv`; derivatives are determined on [0,inf) by uniqueness.
- Regularity: only that f, f', f'' are differentiable within [0,inf) (third derivative f3 exists); no continuity of f''' assumed (weakest natural reading).
- ODE: f3 x + f x * f2 x + (1/2)(1 - (f1 x)^2) = 0 for all x in Ici 0, including x = 0 (one-sided).
- BCs: f 0 = 0, f1 0 = 0, Tendsto f1 atTop (nhds 1).
- Bounds: W/U hypotheses `-1 <= f1 x <= 1` for all x in Ici 0 (non-strict). E: `0 <= f1 x < 1` on Ici 0.
- Wall shear = f2 0; strict inequalities 0.927680039 < f2 0 < 0.927680040 (real literals).
- W: universally quantified over solution tuples. U: conclusion f=g, f1=g1, f2=g2 on Ici 0 (f3 not asserted).
- E: existential over (f,f1,f2,f3) with IsSol, plus bounds and wall-shear window.
- Values outside [0,inf) unconstrained (functions ℝ → ℝ).
