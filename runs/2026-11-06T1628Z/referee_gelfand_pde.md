VERDICT: STANDS

# Referee report: `Work.Math.GelfandPDE.gelfand_pde_radial_bound`

Scope. I read `Work/Math/GelfandPDE.lean`, the statement of `Checked.Math.Gelfand.gelfand_ball_critical` (lines 33–46 of `Checked/Math/Gelfand.lean`), and the Mathlib sources `Mathlib/Analysis/InnerProductSpace/Laplacian.lean`, `.../CanonicalTensor.lean` (one lemma) and `Mathlib/Analysis/Distribution/DerivNotation.lean` (the `Laplacian` class and notation). I read no other repo source. I also elaborated the frozen statement with `lake env lean` from a scratch file in `/tmp/gelfand_ref/` that imports `Work.Math.GelfandPDE`. Scratch scripts are in `/tmp/gelfand_ref/` (`lam.py`, `check.py`, `Elab.lean`, `Elab2.lean`).

## 1. Truth: TRUE

**Reduction (my own derivation).** Take λ > 0 and u as in the hypotheses. Write g(r) = u(r e₁) for r ∈ [0,1].
- g is C² on [0,1) and continuous on [0,1] (from `hu`, `hc` and `hrad`), and g(1) = 0 (from `hb`).
- u(x) = u(−x), so ∇u(0) = 0 and g′(0) = 0.
- On 0 < r < 1, Δu = g″ + (2/r)g′, which gives g″ + (2/r)g′ + λe^g = 0.
- Put a = g(0), k = √(λe^a) and w(s) = g(s/k) − a. Then w″ + (2/s)w′ + e^w = 0, w(0) = 0 and w′(0) = 0.

By uniqueness of the regular solution of this singular IVP, w is the Emden–Chandrasekhar function. That solution exists for all s ≥ 0: w is decreasing, so e^w ≤ 1. From g(1) = 0 we get w(k) = −a, so λ = k²e^{−a} = k²e^{w(k)} ≤ sup_{s≥0} s²e^{w(s)} = λ*. For λ ≤ 0 the conclusion is immediate.

The Checked theorem holds for every S ≥ 41/10, so with S = max(k, 41/10) it bounds s²e^{w(s)} on all of [0, S] by 3.321992119. This covers k < 41/10 too.

**Numerics (independent).**
- *mpmath, 40 digits.* I took the Taylor series at 0 to order s¹²⁰ (tail ≈ 4e−100 at s = 0.5), then used mpmath's Taylor `odefun` and solved 2 + s w′(s) = 0 with `findroot`. Results:
  - s₁ = 4.071496844298139332872138955937
  - **λ\* = 3.321992118339823991255190237568**
  - The same digits come out at 25 digits of working precision.
- *scipy cross-check.* DOP853 at rtol 2.2e−14, run to s = 2000, gives λ\* = 3.321992118339764 (agrees to 13 digits). The critical points of s²e^w are:

  | s | s²e^w | type |
  |---|---|---|
  | 4.0715 | 3.3220 | max |
  | 37.53 | 1.6642 | min |
  | 428.9 | 2.1085 | max |

  After that the values oscillate towards 2, so the first maximum is the global supremum.
- **Margin:** 3.321992119 − λ\* = **6.60e−10**. The lower bound 3.321992118 sits 3.40e−10 below λ\*. Both agree with the certified Checked enclosure, and s₁ lies inside [4.071496844, 4.071496845].

## 2. Vacuity / triviality: NOT VACUOUS, NO JUNK LOOPHOLE

- **Hypotheses can hold with λ > 0.** Take u(x) = w(k‖x‖) − w(k) for any k ∈ (0, s₁]. w(s) = W(s²) with W smooth: the series has only even powers, and the ODE in t = s² is 4tW″ + 6W′ + e^W = 0, which is regular-singular with an analytic solution. So u is C^∞ on ℝ³ (radial, zero on the sphere), and λ = k²e^{w(k)} sweeps (0, λ\*]. At k = s₁ this gives λ = λ\*, so the bound is attained up to its 6.6e−10 slack.
- **Δ.** `Δ` elaborates (checked with pp.explicit under the actual imports) to `Laplacian.laplacian` via `InnerProductSpace.instLaplacian`, the only `Laplacian (E → F)` instance in Mathlib. The definition is `tensorIteratedFDerivTwo ℝ f x (canonicalCovariantTensor E)`. By `laplacian_eq_iteratedFDeriv_orthonormalBasis` and `canonicalCovariantTensor_eq_sum`, this equals ∑ᵢ D²f(x)(eᵢ, eᵢ) for any orthonormal basis, i.e. ∑ ∂²f/∂xᵢ² for the L² basis of `EuclideanSpace`.
  - It uses the global `fderiv`. At a point of the open ball, u is C² on a neighbourhood, so `fderiv (fderiv u) x` only depends on u near x. There is no junk value there.
  - Outside the ball, Δu is junk, but `hpde` only constrains the open ball.
- **`ContDiffOn ℝ 2`.** The order elaborates to `(2 : WithTop ℕ∞)`, which is `rfl`-equal to `((2:ℕ) : WithTop ℕ∞)`. That is genuine C² (ω is a separate value), on an open set.
- **Other conventions.** `Real.exp` is the honest exponential. The constant is `OfScientific` on ℝ, equal to 3321992119/10⁹ (checked by `norm_num`). `ball`/`closedBall` use the Euclidean norm.
- **Boundary and radial hypotheses.** `hb` (all x with ‖x‖ = 1) is consistent with `hrad`: the sphere lies in the closed ball. Neither hypothesis restricts u outside the closed ball, which is harmless. `hrad` with an arbitrary g : ℝ → ℝ only constrains g on [0,1], and that is exactly radial symmetry.
- **Axioms.** `#print axioms` shows only `sorryAx` plus the standard three, as expected for the frozen `sorry`.

## 3. Near misses

- **Constant replaced by 3.3219921: FALSE.** The counterexample is λ = λ\* with u(x) = w(s₁‖x‖) − w(s₁), and λ\* − 3.3219921 = 1.83e−8 > 0. Any constant below λ\* ≈ 3.32199211834 makes the statement false. 3.321992119 sits 6.6e−10 above λ\*, so the margin is tight but correct.
- **Radial hypothesis dropped: still TRUE, not open.**
  - For λ > 0, Δu = −λe^u < 0, so u > 0 in the ball by the strong maximum principle.
  - Gidas–Ni–Nirenberg (1979) then makes u radial. GNN's Theorem 1 assumes u ∈ C²(Ω̄); the C²(Ω) ∩ C(Ω̄) case is covered by the Berestycki–Nirenberg (1991) moving-plane version.
  - It is also covered by the general Brezis–Cazenave–Martel–Ramiandrisoa theory: no solutions (even weak ones) for λ > λ\*.
  - Without `hrad` the statement is therefore true but much harder to formalize (moving planes). Keeping `hrad` is the right call.
- **Weak solutions.** The singular solution −2 log‖x‖ at λ = 2 is excluded by C², and it lies below λ\* anyway.

## 4. Fidelity: FAITHFUL, NO OVERCLAIM

- The module docstring and the theorem docstring describe the hypotheses and conclusion exactly as stated.
- The docstring says "u : ℝ³ → ℝ"; in Lean this is `EuclideanSpace ℝ (Fin 3)`, which is fine.
- It explicitly disclaims existence below λ\*, GNN symmetry, and non-radial and weak solutions. It claims nonexistence only above the bound and only for radial classical solutions.
- "Only Mathlib definitions occur in the statement": confirmed by elaboration under the actual imports. `Work.Math.RadialLaplacian` and `Work.Math.GelfandODEBound` do not shadow `Δ`, `ball`, `exp` or the numerals.
- Minor nit, wording only: line 13 says solutions "with k < 41/10 that the ODE statement does not see". The Checked statement does cover them, since its max is over all of [0, S]. The sentence presumably means "does not mention explicitly".

## 5. Prior art

- λ\* ≈ 3.32 is the classical Frank-Kamenetskii critical parameter for a sphere (δ_c ≈ 3.322), obtained by numerically integrating the Emden–Chandrasekhar equation.
- Joseph & Lundgren (ARMA 49, 1973) describe the radial branch for 3 ≤ N ≤ 9: infinitely many turning points, oscillating around λ = 2(N−2) = 2 for N = 3. This matches my critical values 3.32 / 1.66 / 2.11 / … → 2.
- Gidas–Ni–Nirenberg (1979) gives radial symmetry of positive solutions.
- In my searches I found no rigorous or interval-arithmetic enclosure of λ\* for the 3-ball in the literature, and no formal (Lean, Coq, Isabelle) proof of this nonexistence statement. That is absence of evidence from a short search, not a survey.
- The repo's own `Checked.Math.Gelfand.gelfand_ball_critical` is, as far as I can tell, the only certified enclosure.

Sources consulted:
- arXiv 2207.03166 (read): gives no λ\* value; states λ_s = 2(N−2).
- arXiv 2410.12553v3 (read): cites Joseph–Lundgren, gives λ\* > 2 for d = 3 but no digits.
- en.wikipedia "Frank-Kamenetskii theory" (read): numerical value missing from the fetched text.
- Search-result listings only, not read: the Joseph–Lundgren record on portal.mardi4nfdi.de, and a search for Lean/validated-numerics work, which returned nothing relevant.

## Recommendations (non-blocking)

- None required for the statement.
- Optionally reword docstring line 13 ("does not see" → "does not mention").
- The proof must handle λ ≤ 0 trivially, establish g′(0) = 0 and the ODE uniqueness at the singular point, and apply the Checked theorem with S = max(k, 41/10).
