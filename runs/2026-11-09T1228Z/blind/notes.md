# Interpretation notes
- Solution = f : R -> R, only its values on [0,inf) matter; derivatives via derivWithin on Ici 0 (one-sided at 0), defined as d1, d2, d3.
- Regularity: ContDiffOn R 3 f (Ici 0) (C^3 on the half-line, so f''' exists and is meaningful).
- ODE required for all eta >= 0 (including 0, one-sided), with beta = -1/10 written as (-1/10 : R).
- BCs: f 0 = 0, d1 f 0 = 0, Tendsto (d1 f) atTop (nhds 1).
- "f'' > 0 on the whole half-line": forall eta >= 0, 0 < d2 f eta.
- Decay hypothesis: forall M : R, eventually (atTop) M*(1 - d1 f eta) <= d2 f eta, literal.
- Window: strict inequalities with decimals as rationals 3192697598/10^10 and 3192697599/10^10.
- Claim 2: only the upper bound, strict.
- Proofs are sorry.
