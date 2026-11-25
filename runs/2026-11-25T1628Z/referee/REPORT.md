# Referee report (Opus subagent, run 2026-11-25T1628Z; final message, verbatim up to markdown layout)

VERDICT: STANDS. The statement is correct, the numbers check out independently, and the route works with no real gap. The only change I suggest is optional: name the half-step quotient (x_{k+1}/x_k) explicitly in the plan.

Scope: read only BRIEF.md and runs/2026-11-25T1628Z/lean/BonnorEbertTurningRatio.lean; no Lean run; scripts in runs/2026-11-25T1628Z/referee/scripts/ (algebra.py, numerics.py).

1. Attack on the statement
- Docstring match: the last two conjuncts say what the docstring says (Tendsto (ξ(k+1)/ξ k) atTop 𝓝(exp(2π/√7)); Tendsto ((m(ξ(k+1)) − √(2/π)) / (m(ξ k) − √(2/π))) atTop 𝓝(−exp(−(π/√7)))). The expression for m is the same everywhere; 4πm² = s⁴W'²e^W = u v³ holds.
- ξ is pinned to the extrema: StrictMono and Tendsto atTop make the segments cover [0,∞); with the monotone segments the strict local extrema of m on (0,∞) are exactly {ξ_k}, in order, and ξ is unique.
- No junk division: m(ξ_{2k+1}) < √(2/π) < m(ξ_{2k}) means no denominator is ever zero.
- Direction and sign: both limits k → ∞, k+1 over k; deviations alternate in sign, fits −exp(−π/√7).
- Right constants for the mass, not for λ: linearisation at (1,2) is [[−1,−1],[2,0]], eigenvalues (−1 ± i√7)/2 in t = log s; mass extrema are the zeros of g = 2u − v, simple, twice per period 4π/√7, so the radius ratio is e^{2π/√7}; amplitude decays as e^{−t/2}, factor per half-period −e^{−π/√7}. λ = uv has d log λ/dt = 2 − v, turning points at zeros of v − 2: different radii.

2. Numbers
- Own Taylor-series integrator (order 40–50) for s u' = u(3−u−v), s v' = v(u−1) in t = log s, from s = 0.05 with the 60-term Lane–Emden series; zeros of g by bisection plus Newton. Two independent runs (40 digits, order 40, h = 0.05; 50 digits, order 50, h = 0.025) agree to about 1e-33 relative for k ≤ 15.
- ξ0 = 6.450751444174073658…, inside [6.4507514, 6.4507515]; m(ξ0) = 1.1822265884995997…

| k | ξ_k | m(ξ_k) − √(2/π) | ξ_k/ξ_{k−1} | deviation quotient |
|---|---|---|---|---|
| 1 | 67.00754871959523971916 | −1.035e-1 | 10.387557062071 | −0.269338329442 |
| 4 | 84506.32897574492583913 | 3.027e-3 | 10.765642064954 | −0.306094554153 |
| 8 | 1127777279.202881716954 | 2.618e-5 | 10.749228515733 | −0.305019459686 |
| 12 | 15055955866750.34313391 | 2.266e-7 | 10.749088253567381 | −0.305010173882480 |
| 15 | 18699201371601087.20159 | −6.429e-9 | 10.749086994420539 | −0.305010090515233 |

- Targets: exp(2π/√7) = 10.74908702916350546780, −exp(−π/√7) = −0.30501009281554283878. Both quotients oscillate around their targets, error shrinking by about 0.305 per step. Sign pattern (+ even k, − odd k) matches.

3. Route
- (a) d log(uv³)/d log s = 2u − v = g. At g = 0: y = 2x, Nw = 32x², uv³ = 8u⁴, m = √(2/π)u². s·g' at g = 0 is 8u(1−u), nonzero since Nw > 0; zeros of g are simple sign changes, exactly the ξ_k.
- (b) 1 − cos²θ = 7g²/(8Nw) (8Nw − (6x+5y)² = 7(2x−y)²). At a zero of g, cos θ = −σ·sign(x); the sign of g' forces θ = 0 at the left zero and π at the right zero; x changes sign between consecutive zeros. Identity 28(y−2x)Lq = (6x+5y)Dq − 2Nw(6ẋ+5ẏ) exact; Dq = s·dNw/ds. s·dθ/ds = 2√7 Lq/Nw using σg > 0 inside. Lq − Nw/4 = 2x²y + xy², cubic.
- (c) dθ/dt ∈ √7/2 ± 6√7ε, 6√7 ≈ 15.87 ≤ 16; d log Nw/dt ∈ [−1−36ε, −1+36ε]. As ε → 0: L_k → 2π/√7; ΔlogNw = 2 log|x_{k+1}/x_k| → −2π/√7; x alternates in sign, so x_{k+1}/x_k → −e^{−π/√7}; the deviation quotient is (x_{k+1}/x_k)·(2+x_{k+1})/(2+x_k), second factor → 1.
- Gaps: none of substance. In Lean: θ continuous on the closed segment, differentiable only inside (use an interior-derivative lemma); write down why x alternates; segment bounds only once ξ_k ≥ 300000 (fine, limits are eventual).

4. Prior art (from memory, not checked; the fetch of arxiv.org/pdf/astro-ph/0103159 was blocked)
- Chandrasekhar 1939 (Ch. IV): (u,v) spirals into (1,2) like s^{−1/2}cos((√7/2)log s + δ); both constants follow in a line. Chavanis 2002 (A&A 381, 340) and Lombardi–Bertin discuss the asymptotic spacing of the spiral's turning points; not confirmed whether they state both constants for the mass extrema. No formal verification of either limit known.
