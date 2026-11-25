# Referee report (Opus, run 2026-11-25T0428Z), as returned

**Verdict: STANDS.** The last conjunct is stated correctly and the limit −exp(−π/√7) is right. The planned route works. It needs two small clarifications, neither of which affects the statement.

Read only BRIEF.md and lean/GelfandTurningRatio.lean. Did not run Lean. Scripts: `scripts/turning_ratio.py`, `scripts/focus_constants.py`, `scripts/first_order.py`.

## 1. Attack on the statement
- What the conjunct says: (λ(ζ(k+1)) − 2)/(λ(ζ k) − 2) → −Real.exp(−(Real.pi / Real.sqrt 7)) along ℕ. Bracketing correct; consecutive turning values, shift k+1 over k as in the docstring; sign right (deviations alternate, every quotient negative).
- ζ pinned: ζ strictly monotone, tends to ∞; the intervals [0,ζ0], [ζ_{2k},ζ_{2k+1}], [ζ_{2k+1},ζ_{2k+2}] cover [0,∞), λ strictly monotone on each with alternating direction, so the strict local extrema of λ on (0,∞) are exactly {ζ_k}, in order; ζ is unique. They are the zeros of 2 + sW′ (transversal: at y = 0, ẏ = 2x ≠ 0 since the equilibrium is not reached in finite time).
- Division by zero: impossible, λ(ζ(2k+1)) < 2 < λ(ζ(2k)).
- Real.sqrt 7, Real.pi: standard meaning. Hypotheses force the regular solution (refereed before).

## 2. Is the limit right?
- By hand: in t = log s, u̇ = u(3−u−v), v̇ = v(u−1); Jacobian at (1,2) [[−1,−1],[2,0]], eigenvalues (−1 ± i√7)/2; consecutive zeros of y = v − 2 half a rotation apart, Δt = 2π/√7, amplitude factor e^{−π/√7}; at y = 0, λ − 2 = 2x, sign of x flips each half turn: limit −e^{−π/√7} = −0.3050100928155428387778….
- Numerics: own Taylor integrator in t (order 40 and 48, 60–70 digits, mpmath), start from the power series of W at s0 = 10⁻³ or 5·10⁻⁴; two runs agree on every λ_k to about 1e−61. Known values reproduced (ζ0 = 4.07149684429…, λ0 = 3.32199211834…, λ1 = 1.66415619…, λ2 = 2.108541…, λ3 = 1.967466…, λ4 = 2.009976…, λ5 = 1.996962…, λ6 = 2.000927…), all inside the brackets.

| k | λ_k − 2 | q_k | q_k − L |
|---|---|---|---|
| 0 | 1.3220 | −0.254044 | 5.1e−2 |
| 3 | −3.2534e−2 | −0.306641 | −1.6e−3 |
| 6 | 9.2707e−4 | −0.304964 | 4.6e−5 |
| 9 | −2.6303e−5 | −0.3050114015 | −1.3e−6 |
| 12 | 7.4636e−7 | −0.30501005568 | 3.7e−8 |
| 15 | −2.1178e−8 | −0.305010093869 | −1.05e−9 |

- (q_k − L)/(λ_k − 2) settles at 0.0497552 from k ≈ 5: distance O(|λ_k − 2|); a first-order half-turn perturbation integral (first_order.py) predicts 0.04975515619. ζ_{k+1}/ζ_k → e^{2π/√7} ≈ 10.749.

## 3. The route
- x = u−1, y = v−2: ẋ = −x − y − x(x+y), ẏ = 2x + xy.
- Jordan basis correct: p = √7x, q = x + 2y, Nw = p² + q²; linear part [[−1/2, −√7/2], [√7/2, −1/2]].
- Ṅw + Nw = −4x(4x² + 4xy − y²) exactly; d(log Nw)/dt = −1 + c1(θ)√Nw, sup|c1| = 0.71619.
- θ̇ = √7/2 + c2(θ)√Nw, c2 = p(−3p² + 2√7pq + 7q²)/14 on the unit circle, sup|c2| = 0.25459.
- Nw strictly decreasing for √Nw < 1.39; θ̇ > 0 for √Nw < 5.19.
- At y = 0: Nw = 8x², λ − 2 = 2x. Correct.
- y = 0 is the line q = p/√7 through the origin (exact): consecutive zeros of y exactly π apart in a lifted angle.
- Gap 1 (minor): the angle cannot literally be arccos(p/√Nw) (not a lift: derivative −θ̇ where q < 0); use a continuous lift or the arccos of the cosine of the angle to the starting ray of y = 0, monotone from 0 to π over each half turn.
- Gap 2 (wording): "the logarithm of the radius" must mean log s; log √Nw decreases by π/√7.
- Assumption to confirm: BEFocus supplies entry into the small ball (hence Nw → 0); not checked (not allowed to read).

## 4. Prior art (from memory, nothing looked up)
- Linearisation of Milne's homology variables at (1,2), exponents (−1 ± i√7)/2: Emden; Chandrasekhar 1939; Joseph–Lundgren 1973; the Bonnor–Ebert / Katz / Padmanabhan spiral literature (ratio e^{2π/√7} ≈ 10.75 between successive critical density contrasts). The asymptotic λ_k − 2 ∼ C(−1)^k e^{−kπ/√7} follows and is stated at least implicitly; no precise citation of this exact limit. No formal verification known.
