# Brief: target 1, Clay Navier–Stokes, alternatives (C) and (D) (blind reading)

You are a blind reader for a formal-verification audit. You have not seen, and must not look for, any
Lean formalization of this problem. Read only this brief. No web, no other files, no git.

Source: C. Fefferman, "Existence and smoothness of the Navier–Stokes equation", the Clay Mathematics
Institute's official problem description (claymath.org navierstokes.pdf), as rendered by a fetch
(equations in LaTeX, prose paraphrased where marked):

(1) ∂_t u_i + Σ_{j=1}^n u_j ∂_j u_i = ν Δ u_i − ∂_i p + f_i(x,t), for x ∈ ℝ^n, t ≥ 0.
(2) div u = Σ_{i=1}^n ∂_i u_i = 0, for x ∈ ℝ^n, t ≥ 0.
(3) u(x,0) = u°(x), for x ∈ ℝ^n.
 [paraphrase] u° is a given C^∞ divergence-free vector field on ℝ^n, f_i are the components of a given
 external force, ν > 0 is the viscosity, Δ is the Laplacian in the space variables.
(4) |∂_x^α u°(x)| ≤ C_{αK} (1+|x|)^{−K} on ℝ^n, for any α and K.
(5) |∂_x^α ∂_t^m f(x,t)| ≤ C_{αmK} (1+|x|+t)^{−K} on ℝ^n × [0,∞), for any α, m, K.
(6) p, u ∈ C^∞(ℝ^n × [0,∞)).
(7) ∫_{ℝ^n} |u(x,t)|^2 dx < C for all t ≥ 0 ("bounded energy").
 [paraphrase] a solution is physically reasonable only if it satisfies (6) and (7).
(8) u°(x + e_j) = u°(x), f(x + e_j, t) = f(x,t) for 1 ≤ j ≤ n (e_j the j-th unit vector): the periodic
 setting. Errata: "The further condition p(x + ej, t) = p(x, t) should be made explicit in Eqn (8)."
(9) |∂_x^α ∂_t^m f(x,t)| ≤ C_{αmK} (1+|t|)^{−K} on ℝ^3 × [0,∞), for any α, m, K.
(10) u(x,t) = u(x + e_j, t) on ℝ^3 × [0,∞), for 1 ≤ j ≤ n.
(11) p, u ∈ C^∞(ℝ^n × [0,∞)).
 [paraphrase] in the periodic setting a solution is physically reasonable if it satisfies (10), (11).

(C) "Breakdown of Navier–Stokes solutions on ℝ³": take ν > 0, n = 3. Then there exist a smooth
divergence-free u° on ℝ³ and a smooth f(x,t) on ℝ³ × [0,∞), satisfying (4) and (5), for which "there exist
no solutions (p, u) of (1), (2), (3), (6), (7) on R3 × [0,∞)".
(D) "Breakdown of Navier–Stokes Solutions on ℝ³/ℤ³": take ν > 0, n = 3. Then there exist a smooth
divergence-free u° on ℝ³ and a smooth f(x,t) on ℝ³ × [0,∞), satisfying (8) and (9), for which there exist
no solutions (p, u) of (1), (2), (3), (10), (11) on ℝ³ × [0,∞).

Task: one Lean 4 file (Mathlib only) at runs/2026-11-26T1529Z/T1/reading.lean with your definitions (each
with a doc comment quoting the condition it encodes) and
  theorem reading_C (ν : ℝ) (hν : 0 < ν) : <(C)> := by sorry
  theorem reading_D (ν : ℝ) (hν : 0 < ν) : <(D)> := by sorry
Space is `EuclideanSpace ℝ (Fin 3)`. Avoid junk values (derivatives of non-differentiable functions,
integrals of non-integrable functions, ...): say in a comment how each is excluded. Then, in a comment
block at the end, list every ambiguity and the reading you chose.
