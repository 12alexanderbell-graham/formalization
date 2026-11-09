# Falkner–Skan with adverse pressure gradient (β < 0): what to certify next

Run 2026-11-09T0428Z, research note. Scratch scripts: `/tmp/fsneg/*.py` (not in the repository).
Nothing here was compiled; the Lean sketches in §5 are untested statements to freeze.

## 0. Findings in one screen

1. **The program's bounded-class headline is false for β < 0, and so is the paraphrased "unique in 0 ≤ f' ≤ 1".**
   At β = −0.1 every wall shear α ∈ [α_l, α_u] = [−0.1405…, 0.3193…] gives a solution with f'(∞) = 1.
   In the interior, 1 − f' ~ C η^{2β} (algebraic, ∫(1 − f') = ∞). For α ∈ (0, α_u] the solution has 0 ≤ f' < 1 and f'' > 0.
   So there is a continuum of solutions in the class 0 ≤ f' ≤ 1. Uniqueness needs a decay condition (§2).
2. **The undershoot event cannot happen for β < 0.** When q = 0 and |p| < 1, q' = |β|(1 − p²) > 0, so q never returns to 0 while |p| < 1.
   The Under/Over pair therefore does not bracket anything. The replacement is a **Slow** event: entry into a forward-invariant region {q < μ(1 − p)} (§3).
3. **Proved here in full (elementary, written to be formalized):**
   - Theorem U: uniqueness in the class "q > 0 on [0,∞), p → 1, q ≥ M(1 − p) eventually for every M", for **every** β < 0.
   - The certified-shooting existence of both Stewartson solutions at β = −1/10 (upper with f''(0) > 0; lower with f''(0) < 0 and reversed flow).
     This rests on five lemmas: invariance, limit, Riccati upgrade, Crocco no-crossing and dip comparison.
   The program's cooperative comparison (`CroccoCompare.compare`) fails for β < 0. It is replaced by a no-crossing lemma plus a tail estimate.
4. **Numbers** (32 digits, two independent methods): see the table in §1.
5. **Recommended first freeze:** Theorem U (pure analysis, no certified data) and the cheap non-uniqueness theorem (two certified trajectories with large margins). Then the upper-branch window and existence, then the lower branch (§5).

## 1. Float study

### 1.1 Scaling (confirmed)
For β < 0 let c = √|β| and set F(s) = c f(s/c), P(s) = f'(s/c), Q(s) = f''(s/c)/c.
This is exactly `FSScale.scale` with a = 1, b = β, so a/c² = 1/|β| and b/c² = −1. Then
F''' + K F F'' − (1 − F'²) = 0 with K = 1/|β|, that is, f' = p, p' = q, q' = −K f q + 1 − p².
Equivalently, F(s) = f(s/c')·c' with c' = 1/√|β| gives the same equation; the task text's "c = 1/√|β|" is right only in that form.
With `FSScale`'s convention c = √|β| (as in `TenthBounded`, c = 1/√10 = √(1/10)). In scaled variables F''(0) = f''(0)/√|β| and s = √|β| η.
The scaled pressure term has the **opposite sign** from the program's K-rows (`-(10*f*q) - 1 + p^2` becomes `-(10*f*q) + 1 - p^2`).

### 1.2 Wall shear f''(0)
- Method M1 is bisection on the event classification Over / Slow (the same logic as the certification, §3). It uses μ = √(2|β|) unscaled, its own Taylor-series integrator (degree 30, step 1/8) and 40 digits.
- Method M2 is a secant iteration on the matching condition q = r₊ (1 − p) at η∞. Here r₊ = (f + √(f² − 4|β|(2 − (1−p))))/2 is the fast root of the Riccati equation in §3. M2 uses degree 40, step 1/10, 60 digits and η∞ ∈ {13, 15, 17, 18, 19}.
- The M2 values at the larger η∞ lie inside the M1 brackets.

| β | branch | f''(0) (digits trusted) | M1 bracket ends (last digits) | M2 | scaled F''(0) = f''(0)/√|β| |
|---|---|---|---|---|---|
| −0.1 | upper | 0.31926975984254337011894020350357 | …0350357264 / …0350358053 | …03503573228 (η∞=15) | 1.0096196291173984457979707684536 |
| −0.1 | lower | −0.14054621297867156709766430612410 | …612410441 / …612409455 | …6124102910 (17), …6124102911 (19) | −0.44444614952372023056645781401113 |
| −0.15 | upper | 0.21636140564711143644399544524746 | …4524746023 / …4524746812 | …45247463950 (15) | 0.55864274722219330345737546561278 |
| −0.15 | lower | −0.13342123789528869656646302386069 | …2386068894 / …2386067908 | …23860686217 (18) | −0.34449215493255402082997414847036 |

Notes on these numbers:
- M2 converges like e^{−(η∞−δ)²/2}. At η∞ = 13 the lower branch is wrong in the 18th digit (δ_l ≈ 4.9). This is why the lower branch needs a longer horizon everywhere (§3.5).
- The upper value at −0.1 agrees with the classical tabulated 0.31927.

### 1.3 Shape (double precision, DOP853, rtol 1e−13, grid 1e−4; δ from the 45-digit runs)

The table gives the β = −0.1 values, with the β = −0.15 values in brackets.

| | upper branch | lower (Stewartson) branch |
|---|---|---|
| f'' | > 0 on [0,∞) | < 0 on [0, 1.4323) [0.8939], > 0 after |
| f' | 0 < f' < 1 on (0,∞) | < 0 on (0, 2.8029) [1.7786] (reversed flow), min −0.100219 [−0.059564], then increases to 1 |
| f | > 0 on (0,∞) | < 0 on (0, 4.135) [2.6572], min −0.18832 [−0.07073], then > 0 |
| f''' | one sign change, + → − at 1.0984 [1.4869]; max f'' = 0.39416 [0.37303] | one sign change at 4.664 [3.6132]; max f'' = 0.34672 [0.35755] |
| δ = lim(η − f) | 1.44269679609308837 [1.64696954388842103] | 4.89510767253305914 [3.73974387528198808] |

Both branches satisfy |f'| < 1 everywhere, so the lower branch lies in the program's class −1 ≤ f' ≤ 1.

### 1.4 Approach to 1
Linearize with g = 1 − f'. Then g'' + f g' − 2βg + βg² = 0 and f = η − δ + (exponentially small). Write x = η − δ.
The two decaying modes are:
- the **Gaussian** mode, x^{−1−2β} e^{−x²/2} (1 − (1+2β)(2+2β)/(2x²) + O(x^{−4})), a parabolic-cylinder function;
- the **algebraic** mode, x^{2β}.

Both modes decay because β < 0. This is the source of the continuum.

- The two Stewartson solutions have pure Gaussian tails, 1 − f' ≈ A x^{−1−2β} e^{−x²/2}, with q/(1 − p) ≈ x → ∞.
  - Extrapolated A (3 digits): β = −0.1: A_u ≈ 0.3337, A_l ≈ 0.3054. β = −0.15: A_u ≈ 0.3389, A_l ≈ 0.329.
  - The fitted 1/x² coefficient of the upper branch is −0.72·A, which matches (1+2β)(2+2β)/2 = 0.72.
- Interior α gives 1 − f' ~ C η^{2β}. Measured local log-slopes at α = 0.3 for η = 20…320 are −0.2135, −0.2071, −0.2040, −0.2025 (limit −0.2). Also η q/(1 − p) → 0.20 and η − f → ∞.
- Crocco ordering check: q at fixed levels p = 0.2, 0.5, 0.9, 0.99 increases with α. For α < α_u the level p = 0.99 is not reached by η = 400.

### 1.5 Global picture of the shooting map at β = −0.1 (α = f''(0))
- α < α_c ≈ −0.26: p → −∞.
- α_c < α < α_l: dips, then overshoots p = 1.
- α_l ≤ α ≤ α_u: p → 1 with p < 1. The tail is Gaussian only at the endpoints, algebraic inside.
- α > α_u: overshoots.

The Stewartson pair is the **boundary** of the no-overshoot interval. At β = −0.15 no blow-down occurs for α ≥ −0.3.

## 2. Uniqueness in a class

Scaled system (S_K): f' = p, p' = q, q' = −K f q + 1 − p² on [0,∞), K > 0, f(0) = p(0) = 0. A BVP solution additionally has p → 1.
- Class 𝓜 ("monotone"): q > 0 on [0,∞). This is the program's `hpos`.
- Class 𝓔 ("Gaussian tail"): for every M, eventually q ≥ M(1 − p). Then 1 − p ≤ C_M e^{−Mη} for every M.

**Negative results.**
- Uniqueness in {0 ≤ p ≤ 1} fails (continuum, §1.5). It is certified cheaply in §3.6.
- Uniqueness in {−1 ≤ p ≤ 1} ∩ 𝓔 fails: the Stewartson pair, §3.
- Uniqueness in 𝓜 alone fails: α ∈ (0, α_u].

**Lemma 0 (touch, = `LimitCore.touch_one`).** If p(η₀) = ±1 and q(η₀) = 0, then p ≡ ±1. So this cannot happen when p(0) = 0.
Proof: (f(η₀) ± (η − η₀), ±1, 0) solves (S_K) with the same data at η₀, and solutions are unique forward and backward. ∎
Consequence: if p ≤ 1 on [0,∞), then p < 1. At an interior maximum p = 1 we would have q = 0.

**Lemma 1 (no return to q = 0).** If q(η₁) = 0 and |p(η₁)| < 1, then q'(η₁) = 1 − p(η₁)² > 0.
Hence, if q > 0 on [a, η₁) and |p| < 1 on [a, η₁], then q(η₁) > 0. A first zero reached from above would need q'(η₁) ≤ 0.
Here K plays no role; only the sign of the pressure term matters. This is exactly why Under never fires for β < 0.

**Lemma C (class 0 ≤ p ≤ 1).** A BVP solution with 0 ≤ p ≤ 1 has q(0) ≥ 0, p < 1, and q > 0 on (0,∞). So "f'' > 0" holds for every solution in the class.
Proof:
- q(0) < 0 would make p < 0 just right of 0.
- p < 1 follows from Lemma 0.
- If q(0) > 0, Lemma 1 gives q > 0 on [0,∞). If q(0) = 0, then q'(0) = 1, so q > 0 on (0, ε], and Lemma 1 applies from ε. ∎

**Lemma T (Crocco no-crossing; replaces `CroccoCompare.compare`).** The hypotheses:
- K > 0, L > 0;
- z₁, z₂ > 0 and F₁, F₂ continuous on [0,L);
- on (0,L): F_i' = t/z_i and z_i' = −K F_i + (1 − t²)/z_i;
- F₁(0) = F₂(0) and z₁(0) < z₂(0).

Then z₁ < z₂ on [0,L), and E := F₁ − F₂ is nondecreasing on [0,L) with E > 0 on (0,L).

Proof. Let D = z₂ − z₁ and suppose D(t) ≤ 0 somewhere. Let t* be the infimum of such t; then t* > 0, D(t*) = 0 and D > 0 on [0,t*).
- On (0,t*), E' = t(1/z₁ − 1/z₂) > 0, so E(t*) > 0.
- D'(t*) = K E(t*) + (1 − t*²)(1/z₂ − 1/z₁) = K E(t*) > 0, because the pressure term vanishes at a crossing.
- So D(t) < 0 for t slightly below t*, a contradiction.
- With D > 0 we get E' > 0 on (0,L). ∎

Remarks:
- No condition L ≤ 1 is needed here.
- Contrast with `compare`. For β < 0 the pressure term (1 − t²)/z is anti-cooperative, so "D ≥ D(0)" is false.
  Numerically, at β = −0.1 with z₁ = α = 0.3 and z₂ = α_u: D(0) = 0.0193 but D at t = 0.9999 is 3.9·10⁻⁴.

**Theorem U′ (the Gaussian-tail solution has the largest wall shear in 𝓜).** Let K > 0. Let (f₁,p₁,q₁) be a BVP solution in 𝓜 ∩ 𝓔, and let (f₂,p₂,q₂) be any BVP solution in 𝓜. Then q₂(0) ≤ q₁(0).

Proof. Suppose q₁(0) < q₂(0).
- By Lemma 0, p_i < 1. Apply `CroccoMap.crocco` with the pressure sign generalised to each solution on [0,E_i]. This gives inverses ψ_i, z_i = q_i∘ψ_i and F_i = f_i∘ψ_i on [0,L), L = min p_i(E_i) < 1, with ψ_i' = 1/z_i.
- Enlarging E_i does not change these objects on the smaller range.
- Lemma T gives D = z₂ − z₁ > 0 and E nondecreasing with E > 0 on (0,L).
- Put G₁(t) = ψ₁(t) − F₁(t). Then G₁' = (1 − t)/z₁, and G₁ = η − f₁ read at velocity t.

*Step 1.* For 0 < t₀ ≤ t < L: K E(t₀)(t − t₀) ≤ D(t) + 2(G₁(t) − G₁(t₀)).
Let Ψ(s) = D(s) + 2G₁(s) − K E(t₀)s. Then
Ψ' = K(E(s) − E(t₀)) − (1 − s²)(1/z₁ − 1/z₂) + 2(1 − s)/z₁ ≥ (1 − s)²/z₁ + (1 − s²)/z₂ ≥ 0.
Here we use E(s) ≥ E(t₀), 0 ≤ s < 1 and z₂ > 0. So Ψ(t) ≥ Ψ(t₀); then drop D(t₀) > 0.

*Step 2 (tail).* If q₁ ≥ M(1 − p₁) on [η₀,∞) and t₀ = p₁(η₀) ≤ t < L, then G₁(t) − G₁(t₀) ≤ (t − t₀)/M.
Let χ(x) = x − f₁(x) − p₁(x)/M. Then χ' = 1 − p₁ − q₁/M ≤ 0 on [η₀,∞), so χ(ψ₁(t)) ≤ χ(η₀).

*Step 3.* The choices are made in this order:
1. Fix t* = p₁(1) ∈ (0,1) and E* = E(t*) > 0, then M = 4/(K E*).
2. By 𝓔 pick η₀ ≥ 1 with q₁ ≥ M(1 − p₁) on [η₀,∞), and set t₀ = p₁(η₀) ∈ [t*, 1).
3. Let ε = K E*(1 − t₀)/8.
4. Since ∫_T^∞ q₂ ≤ 1 − p₂(T), q₂ < ε somewhere beyond any T. Pick η₂ with p₂(η₂) ≥ (1 + t₀)/2 and q₂(η₂) < ε, and set t = p₂(η₂).
5. Take E₂ > η₂ and E₁ with p₁(E₁) > t, so that t < L.

Then D(t) < z₂(t) = q₂(η₂) < ε, and Steps 1–2 give
K E*(t − t₀) ≤ ε + 2(t − t₀)/M = ε + K E*(t − t₀)/2.
So K E*(1 − t₀)/4 ≤ K E*(t − t₀)/2 ≤ ε = K E*(1 − t₀)/8, a contradiction. ∎

**Theorem U (uniqueness).** For every K > 0, that is every β < 0, two BVP solutions in 𝓜 ∩ 𝓔 coincide. Apply U′ both ways to get q₁(0) = q₂(0); then use IVP uniqueness. ∎

Where each hypothesis is used:
- 𝓜 makes the Crocco map exist from t = 0. Without it the lower branch is a counterexample.
- 𝓔 is needed only for the solution with the smaller shear (Step 2). Without it the algebraic continuum is a counterexample.
- p → 1 is used in Step 3.
- K > 0 is used in Lemma T and Step 3.
- β₀ is not used: for β < β₀ the theorem is vacuous.

A class with 0 ≤ p ≤ 1 instead of 𝓜 also works, with one extra input. Lemma C gives 𝓜 except possibly q(0) = 0, and the Crocco map is singular there. At K = 10 this case is excluded by certifying Slow at α = 0 (§3.6; that solution is algebraic, so it is not in 𝓔).
The integrable class ∫(1 − f') < ∞ is equivalent to 𝓔 for |β| < 1/2. Proof sketch: in the Slow region r = q/(1−p) ≤ 2|β|/((1−ε)η) eventually, so 1 − p ≥ c η^{−2|β|/(1−ε)}. That proof is not needed for the program; 𝓔 is the convenient formal class.

## 3. Existence of two solutions (β = −1/10, scaled K = 10)

### 3.1 Events
Fix μ > 0 and θ = (μ + 2/μ)/K. The proposal is μ = 3, θ = 11/30, so Kθ = 11/3 = 3 + 2/3.
- **Over**(α): ∃ η > 0, 1 < p(η). Drop the program's guard "q > 0 on [0,η]". It is automatic for α > 0, false for the lower branch, and it shrinks the margins (§3.5).
- **Slow**(α): ∃ η > 0, (∀ s ∈ [0,η], p s < 1) ∧ 0 < p η ∧ q η < μ(1 − p η) ∧ θ < f η.

Both events are open in α: strict inequalities at one time and on a compact interval, together with `flow_cont`. The proof of the program's `under_open` / `over_open` carries over.
They are disjoint by Lemma I, given q(η) > 0, which holds in both windows (Lemma 1, Lemma D).
The old **Under** is impossible for α ≥ 0 (Lemma 1), so the program's two-event scheme does not apply.

### 3.2 Lemmas (full proofs)

**Lemma I (Slow region is forward invariant).** Suppose that at η₀:
0 ≤ p < 1, 0 < q < μ(1 − p), f > θ.
Then the same holds on [η₀,∞). In particular p < 1 forever.

Proof. Let η* be the supremum of the set where all four conditions hold on [η₀,η], and suppose η* < ∞.
- On [η₀,η*), q > 0, so p ↑ and p ≥ 0. Hence f is nondecreasing and f ≥ f(η₀) > θ, up to and including η*.
- Let g = 1 − p and W = q − μg. A direct computation with q = W + μg gives
  W' = (μ − Kf)W + g(μ² − μKf + 2 − g).
- The bracket is < μ² − μ(μ + 2/μ) + 2 = 0. So (W·exp∫(Kf − μ))' ≤ 0 and W < 0 on [η₀,η*].
- g' = −q = −W − μg ≥ −μg gives g(η*) ≥ g(η₀)e^{−μ(η*−η₀)} > 0.
- q(η*) > 0 by Lemma 1, and p(η*) ≥ 0.
- All conditions are strict at η*, so by continuity they persist beyond η*, a contradiction. ∎

**Lemma L (limit).** Suppose q > 0 on [a,∞), p(a) > −1 and p < 1 on [a,∞). Then p → 1 and f → ∞.

Proof. p increases to some L ∈ (−1,1]. Suppose L < 1.
- Let c = min(1 − p(a)², 1 − L²) > 0 and B = |f(a)|.
- For η ≥ a: f ≤ B + η and q' ≥ −K(B + η)q + c.
- Let φ = q − c/(2K(B + η)). Wherever φ ≤ 0 we have q' ≥ c/2 and so φ' ≥ c/2 > 0.
- Therefore φ cannot stay ≤ 0 on [a,∞) (it would grow linearly), and once positive it stays positive.
- So q ≥ c/(2K(B + η)) on some [η₁,∞), and p(η) − p(η₁) ≥ (c/2K) log((B+η)/(B+η₁)) → ∞. This contradicts p ≤ 1. ∎

In Lean the last step is monotonicity of p − (c/2K)·log(B + η).

**Lemma R (Riccati upgrade).** Suppose q > 0 and p < 1 on [a,∞), p → 1, and q ≥ μ(1 − p) on [a,∞). Then for every M, eventually q ≥ M(1 − p), i.e. 𝓔 holds.

Proof. Let r = q/(1 − p). Then r' = r² − Kfr + 2 − (1 − p), since 1 − p² = g(2 − g).
- Take M ≥ μ. Since f → ∞, pick a₁ ≥ a with Kf ≥ M + 3/μ on [a₁,∞).
- Suppose r(η₁) < M for some η₁ ≥ a₁.
- r cannot climb back to M: at a first such point r' ≤ M(M − Kf) + 2 ≤ −3 + 2 < 0.
- While μ ≤ r < M we get r' ≤ μ(r − Kf) + 2 ≤ μ(M − Kf) + 2 ≤ −1. So r drops below μ in finite time, a contradiction. ∎

**Lemma D (dip comparison; lower branch only).** Let α₋ < α ≤ 0, with trajectories Y₋ and Y from (0,0,α₋) and (0,0,α). Suppose that on [0,σ], p₋ ≤ 0, p₋ > −1 and q₋(σ) > 0. Then:
- q has a zero τ ≤ σ;
- p ≥ p₋ > −1 on [0,τ];
- q > 0 after τ for as long as |p| < 1 (Lemma 1).

Proof. Let τ be the first zero of q (≤ ∞) and Δ = Y − Y₋. On [0, min(τ,σ)]:
- q ≤ 0, so p ≤ 0 and f ≤ 0; also f₋ ≤ 0.
- Δf' = Δp, Δp' = Δq, and Δq' = −Kq·Δf − Kf₋·Δq − (p + p₋)·Δp.
- All three coefficients are ≥ 0: the system is cooperative in the reversed-flow quadrant p, q ≤ 0.
- Δq(0) = α − α₋ > 0. A first-exit argument as in `compare_window` gives Δq ≥ Δq(0) > 0 and Δp, Δf ≥ 0.
- If τ > σ, then q(σ) > q₋(σ) > 0, which is absurd. So τ ≤ σ and p ≥ p₋ on [0,τ]. ∎

### 3.3 Assembly

**Upper branch.** Window I = [α₋, α₊] = [1.009619629, 1.0096196292] (scaled), with Slow(α₋) and Over(α₊) certified.
- I is connected and Over, Slow are disjoint and open, so some α* ∈ I has neither event.
- Since α* > 0, Lemma 1 gives q > 0 while p < 1. ¬Over and Lemma 0 give p < 1, hence q > 0 on [0,∞).
- Lemma L gives p → 1 and f → ∞. So for large η, Slow's side conditions hold, and ¬Slow forces q ≥ μ(1 − p).
- Lemma R gives 𝓔. So α* is a solution in 𝓜 ∩ 𝓔, and by Theorem U it is the unique one.

**Upper window theorem (every 𝓜 ∩ 𝓔 solution has α₋ < q(0) < α₊).**
- *q(0) ≥ α₊ is impossible.*
  - q(0) = α₊ would overshoot.
  - If q(0) > α₊, apply Lemma T to the solution and to the Over trajectory, which has q > 0 up to its crossing time η_O (Lemma 1).
  - Then (ψ_O − ψ)' = 1/z_O − 1/z > 0 on the common range, so ψ(t) < ψ_O(t) ≤ η_O for t < 1.
  - But t = p(η_O + 1) < 1 has ψ(t) = η_O + 1, a contradiction.
- *q(0) ≤ α₋ is impossible.*
  - Equality would put the solution into the Slow region, contradicting 𝓔 with M = μ.
  - If q(0) < α₋: the α₋ trajectory is in 𝓜 by Lemmas I, L and 1, so Theorem U′ gives α₋ ≤ q(0), a contradiction.

**Lower branch.** Window [α₋, α₊] = [−0.4444461497, −0.4444461493], with Over(α₋) and Slow(α₊) certified. For α₋ also certify the dip data with σ = 3/4: p₋ ≤ 0 on [0,3/4], p₋ ≥ −0.11, q₋(3/4) ≥ 0.3. Measured values: p₋(3/4) = −0.0540, q₋(3/4) = 0.317, f₋(3/4) = −0.0556.
- The same connectedness argument gives a neither-point α*.
- Lemma D gives p > −1 and q > 0 after τ ≤ 3/4. ¬Over and Lemma 0 give p < 1.
- Lemma L (with a slightly after τ) gives p → 1. ¬Slow and Lemma R give 𝓔.
- Since f''(0) = α* < 0, f' < 0 near the wall.
- Together with the upper solution this gives two distinct solutions in {−1 ≤ p ≤ 1} ∩ 𝓔.

Lemma D removes the "p → −1 separatrix" trap. Without it a neither-point could be the codimension-one trajectory with p ↓ −1 (algebraically), which is in neither event. No extra Down event is needed.
Uniqueness of the lower branch in a reversed-flow class is **not** claimed. That is an open, harder target.

### 3.4 Unscaled windows
Through √10 (as in `TenthBounded`):
- upper: 0.3192697598 < f''(0) < 0.3192697599 (images 0.31926975980542 and 0.31926975986866);
- lower: −0.1405462131 < f''(0) < −0.1405462129 (images −0.14054621303442 and −0.14054621290793).

### 3.5 Horizons and margins (scaled K = 10, μ = 3, 40-digit runs, h = 1/32)

| end | event | node s | margin at node |
|---|---|---|---|
| upper α₋ = 1.009619629 | Slow | 3.0 (first at 2.625) | 1 − P = 2.8e−11, 3(1−P) − Q = 8.2e−11, F − θ = 2.2; Q = +2.3e−12 (do not certify Q; use Lemma 1) |
| upper α₊ = 1.0096196292 | Over | 2.75 | P − 1 = 2.0e−11 (peak 2.4e−11 at 2.78); Q = 4e−12, hence drop the guard |
| lower α₋ = −0.4444461497 | Over | 3.75 | P − 1 = 2.2e−10 |
| lower α₊ = −0.4444461493 | Slow | 4.0 | 1 − P = 2.8e−10, 3(1−P) − Q = 8.2e−10, F − θ = 2.1 |

- **Horizons:** about 3 (96 cells) for the upper branch and about 4 (128 cells) for the lower one.
- **Required absolute enclosure at the event node:** ≲ 5·10⁻¹² for the upper branch and ≲ 5·10⁻¹¹ for the lower one.
- **Why the margins are this small:** both decaying modes decay, so an α-error ε stays O(ε) and is never amplified. For β > 0 the bad mode grows. This is the main numerical risk.
- **Fallback (6-digit windows), events with ε = 10⁻⁶:**
  - upper: Over at s ≈ 2.06, Slow at s ≈ 2.16, margins ≈ 1e−7;
  - lower: Over at s ≈ 3.06, Slow at s ≈ 3.16, margins ≈ 1e−6.
- **β = −0.15 (K = 20/3) is harder.** Events with ε = 10⁻¹⁰: upper at s ≈ 3.25–3.34, lower at s ≈ 4.0–4.1. K = 10 is the recommended row.

### 3.6 Cheap non-uniqueness (no windows, no IVT)
Certify Slow for exact scaled α ∈ {0, 1/2, 1}. The first Slow node, then the values a quarter step later:

| α | first Slow node | s | P | Q | 3(1−P) − Q | F |
|---|---|---|---|---|---|---|
| 0 | 1.375 | 1.625 | 0.735 | 0.205 | 0.59 | 0.544 |
| 1/2 | 1.031 | 1.281 | 0.824 | 0.183 | 0.34 | 0.586 |
| 1 | 1.469 | 1.719 | 0.9973 | 9.7e−4 | 7.1e−3 | 1.26 |

Lemmas I, L and 1 then turn each into a BVP solution with 0 ≤ p < 1 and q > 0 on (0,∞).
So with α = 1/2 and α = 1 (both in 𝓜) the class uniqueness fails, with O(0.1) margins and horizon < 2. Degree-12 cells with h = 1/32 are more than enough.
Optional strengthening: by Lemma T and the ψ-comparison above, every α ∈ (0, 1/2] gives a solution, a continuum.

## 4. Prior art (from memory; no search was possible within the allowed web scope, and I fetched nothing)

- K. Stewartson (1954), *Further solutions of the Falkner–Skan equation*, Proc. Camb. Phil. Soc. 50. Reversed-flow branch; he imposes exponential decay. Confident.
- W. A. Coppel (1960), *On a differential equation of boundary-layer theory*, Phil. Trans. R. Soc. A 253. P. Hartman, *Ordinary Differential Equations*, Falkner–Skan chapter. Confident that these treat β < 0 existence and uniqueness of the attached solution.
  I believe their uniqueness statement carries a decay or integrability condition. I could not check this, but §1.5 shows it must, since 0 ≤ f' ≤ 1 alone is not enough.
- S. P. Hastings (1972), *Reversed flow solutions of the Falkner–Skan equation*, SIAM J. Appl. Math. 22. An analytic existence proof of reversed-flow solutions for small |β|. Fairly confident.
- A. H. Craven & L. A. Peletier (1972), Mathematika 19. Two notes, on uniqueness and on reverse flow. Unsure of the exact content.
- P. A. Libby & T. M. Liu (1967), AIAA J. 5. Further (overshooting / algebraic) solutions. Moderately confident.
- W. C. Troy (1979), Quart. Appl. Math. Non-monotone solutions. Moderately confident.
- B. Oskam & A. E. P. Veldman (1982), J. Eng. Math. 16. Branching of solutions for β < 0. Moderately confident.
- **Computer-assisted / interval proofs:** I know of none for the lower branch or for non-uniqueness at a specific β < 0. Rigorous-numerics papers on Blasius-type problems exist (radii-polynomial / Chebyshev-series methods), but I cannot name one on Falkner–Skan β < 0 with confidence. Treat novelty as **unverified**.
  The formal (Lean) certification would in any case be new as far as I know.

## 5. Statements to freeze (sketches in the program's conventions; K-row form)

```lean
-- (A1) pure analysis, any K > 0  [Lemmas 0,1,T + CroccoMap with pressure sign +, Theorem U]
theorem negK_monotone_equal {K : ℝ} (hK : 0 < K) (f p q f₂ p₂ q₂ : ℝ → ℝ)
    (hf : ∀ η ∈ Ici (0:ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0:ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0:ℝ), HasDerivWithinAt q (-(K * f η * q η) + 1 - p η ^ 2) (Ici 0) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = 0) (hlim : Tendsto p atTop (𝓝 1))
    (hpos : ∀ η ∈ Ici (0:ℝ), 0 < q η) (hexp : ∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - p η) ≤ q η)
    -- same hypotheses for f₂ p₂ q₂ (hpos₂, hexp₂)
    : ∀ η ∈ Ici (0:ℝ), f η = f₂ η ∧ p η = p₂ η ∧ q η = q₂ η
-- (A1') the stronger one-sided form actually used later: drop hexp₂, conclude q₂ 0 ≤ q 0.

-- (A2) certified, cheap: non-uniqueness in the monotone class at K = 10 (β = −1/10)
theorem k10neg_not_unique : ∃ f p q f₂ p₂ q₂ : ℝ → ℝ, (system K=10, `+ 1 - p^2`, both) ∧
    f 0 = 0 ∧ p 0 = 0 ∧ q 0 = 1/2 ∧ f₂ 0 = 0 ∧ p₂ 0 = 0 ∧ q₂ 0 = 1 ∧
    Tendsto p atTop (𝓝 1) ∧ Tendsto p₂ atTop (𝓝 1) ∧
    (∀ η ∈ Ici (0:ℝ), 0 < q η ∧ 0 ≤ p η ∧ p η ≤ 1) ∧ (∀ η ∈ Ici (0:ℝ), 0 < q₂ η ∧ 0 ≤ p₂ η ∧ p₂ η ≤ 1)

-- (B) upper row: window + existence (Slow at 1.009619629, Over at 1.0096196292; μ = 3, θ = 11/30)
theorem k10neg_monotone_window (f p q) (…as A1…) : 1.009619629 < q 0 ∧ q 0 < 1.0096196292
theorem k10neg_exists_monotone : ∃ f p q, (…) ∧ hpos ∧ hexp ∧ 1.009619629 < q 0 ∧ q 0 < 1.0096196292
-- unscaled via FSScale (b = −1/10): 0.3192697598 < f''(0) < 0.3192697599

-- (C) the novel target: Stewartson pair at β = −1/10, unscaled
theorem fs_neg_tenth_two_solutions : ∃ f p q f₂ p₂ q₂ : ℝ → ℝ,
    (∀ η ∈ Ici (0:ℝ), HasDerivWithinAt q (-(f η * q η) + 1/10 * (1 - p η ^ 2)) (Ici 0) η) ∧ (…f, p, f₂, p₂, q₂…) ∧
    f 0 = 0 ∧ p 0 = 0 ∧ f₂ 0 = 0 ∧ p₂ 0 = 0 ∧ Tendsto p atTop (𝓝 1) ∧ Tendsto p₂ atTop (𝓝 1) ∧
    (∀ η ∈ Ici (0:ℝ), -1 ≤ p η ∧ p η ≤ 1 ∧ -1 ≤ p₂ η ∧ p₂ η ≤ 1) ∧
    (∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - p η) ≤ q η ∧ M * (1 - p₂ η) ≤ q₂ η) ∧
    0.3192697598 < q 0 ∧ q 0 < 0.3192697599 ∧ -0.1405462131 < q₂ 0 ∧ q₂ 0 < -0.1405462129
```

Infrastructure deltas:
- `CroccoMap.crocco` needs the pressure sign as a parameter.
- New lemmas `no_cross` (T), `slow_invariant` (I), `limit_neg` (L), `riccati_up` (R) and `dip_compare` (D).
- The clamped field becomes `-(10*cl(t+2) f * cl 2 q) + 1 - (cl 2 p)^2`. The clamps are not active: |P| ≤ 1, |Q| ≤ 1.26 and F ≥ −0.06.
- Event definitions per §3.1.

Order: A1 and A2 first, then B, then C (C reuses B and adds Lemma D and the lower data).
