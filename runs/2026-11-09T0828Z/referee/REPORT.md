# Referee report on `runs/2026-11-09T0428Z/research/fs_negative_beta.md`

Referee: subagent (Opus, general-purpose, not a fork; read only the note and the CroccoMap/CroccoCompare/LimitCore conventions). Its Write call was blocked by the harness; the main session saved its returned text here verbatim in substance. Scripts: `scripts/` (algebra.py = sympy identities; taylor.py, shootrun.py, margins.py, dip.py, odecheck.py, longrun.py, remarkT.py = 50/65-digit Taylor integrations and mpmath cross-checks).

**Overall:** no lemma is wrong; every identity confirmed in sympy; every headline number reproduces. Six fixable gaps (three local to L, R, T; ψ′ = 1/z not exported by `crocco`; unclamping of the neither-point never argued; p → 1 redundant in 𝓜). Two float-study remarks are false.

## Verdicts
- **Lemma 0:** CONFIRMED.
- **Lemma 1:** CONFIRMED. The "hence" clause needs a < η₁.
- **Lemma C:** CONFIRMED.
- **Lemma T:** GAP — add continuity of z_i on [0, L) (as in `compare_window`) and K > 0. Rest confirmed: D′ = K·E + (1−t²)(1/z₂ − 1/z₁), so D′(t*) = K·E(t*); F_i(0) = f_i(0) = 0 because ψ_i(0) = 0. Remark value D(0.9999) ≈ 3.94e−4 confirmed.
- **Theorem U′:** CONFIRMED. Step 1: Ψ′ = K(E − E₀) + (1−s)²/z₁ + (1−s²)/z₂ exactly (sympy). Step 2: χ′ = 1 − p − q/M exactly. Step 3: no circularity in the order of choices (ε depends only on E* and t₀), t₀ < t < L holds, E(t₀) ≥ E*, contradiction 1/4 ≤ 1/8. Formal fixes: take ψ_i as the inverse of p_i on [0, 1) (nothing then depends on E_i); export ψ′ = 1/z from `crocco`.
- **Theorem U:** CONFIRMED. p → 1 is redundant in 𝓜 (if p ≥ 1 at η₁ then q′ ≤ 1 − p(η₁+1)² < 0 afterwards, so q reaches 0; hence p < 1 and Lemma L gives p → 1). 𝓜 is necessary (upper/lower pair); 𝓔 on the smaller-shear solution is necessary (α = 1/2 against the upper solution). The 0 ≤ p ≤ 1 variant holds only at K = 10 (needs the certified Slow at α = 0). Do not freeze the integrable-class sketch (only sketched).
- **Lemma I:** CONFIRMED. W′ = (μ − Kf)W + g(μ² − μKf + 2 − g) exact; bracket exactly 0 at f = θ. Wording: 0 ≤ p persists past η* because p(η*) > p(η₀) ≥ 0.
- **Lemma L:** GAP — with a = 0, f(0) = 0 the note's B = 0 divides by zero at η = 0: use B = |f(a)| + 1. f → ∞ stated but not proved (one line). The φ′ ≥ c/2 step is correct (the extra term is +c/(2K(B+η)²) > 0).
- **Lemma R:** CONFIRMED. r′ = r² − Kfr + 2 − g exact; the inequality at r = M needs M ≥ μ; the case M < μ follows by monotonicity in M (not stated). Choosing a₁ is legitimate (p → 1 ⇒ f → ∞).
- **Lemma D:** CONFIRMED. Δq′ = −Kq·Δf − Kf₋·Δq − (p+p₋)·Δp exact; all three coefficients ≥ 0 in the reversed-flow quadrant; first exit and τ ≤ σ valid.
- **§3.3 assembly:** logic CONFIRMED (events open and disjoint; a neither-point lies in 𝓜 ∩ 𝓔 because all Slow side conditions hold at large η, so ¬Slow gives q ≥ μ(1−p) on a tail; the overshoot half of the window theorem needs only 𝓜). **GAP:** nothing proves the clamps inactive for the neither-point on [0, ∞). Upper branch: H = q²/2 + p³/3 − p has H′ = −K f q², giving q ≤ 1.54. Lower branch: an α-interval enclosure up to s = 4 (where F > 0), then H; measured min F = −0.05955 against the note's clamp bound −0.06 (tight).
- **§3.6:** CONFIRMED, including the continuum: every scaled α ∈ (0, 1.009619629] gives a solution (Lemma T against the Slow trajectory at α₋). "O(0.1) margins" is false for α = 1 (≈ 3e−3); α = 3/4 at s = 1.15625 gives 0.107 / 0.13 / 0.228.
- **False remark §1.4:** "p = 0.99 not reached by η = 400 for α < α_u": at unscaled α = 0.3, p passes 0.99 near η ≈ 60 and p(400) = 0.99343.

## Numbers (K = 10; two Taylor configurations at 50 and 65 digits agree; mpmath odefun spot checks)
- Upper F″(0) ∈ [1.009619629117398445797970768453617, …624] (note: 1.0096196291173984 ✓).
- Lower F″(0) ∈ [−0.4444461495237202305664578140111421, …1342] (note ✓).
- Unscaled: 0.31926975984254337012 and −0.1405462129786715671; both inside the planned decimal windows.

First Slow node (grid h = 1/32), margins 1 − P / 3(1−P) − Q / F − θ:

| α | first node | margins | later node | margins |
|---|---|---|---|---|
| 0 | 1.375 | 0.341 / 0.609 / 0.0018 | 1.625 | 0.265 / 0.591 / 0.177 |
| 1/2 | 1.03125 | 0.251 / 0.309 / 0.021 | 1.28125 | 0.176 / 0.345 / 0.219 |
| 1 | 1.46875 | 0.0036 / 0.0018 / 0.64 | 1.71875 | 0.0027 / 0.0071 / 0.89 |

| end | event | where | margin |
|---|---|---|---|
| upper α₋ = 1.009619629 | Slow | first 2.625 (1.9e−12); use s = 3.0 | 1 − P = 2.80e−11, 3(1−P) − Q = 8.16e−11, F − θ = 2.18, Q = 2.26e−12 |
| upper α₊ = 1.0096196292 | Over | crosses p = 1 at s = 2.5531 | P − 1 = 1.98e−11 at 2.75; peak 1.99e−11 at 2.803 |
| lower α₋ = −0.4444461497 | Over | 3.75 | P − 1 = 2.24e−10 |
| lower α₊ = −0.4444461493 | Slow | 4.0 | 1 − P = 2.80e−10, 3(1−P) − Q = 8.17e−10, F − θ = 2.09 |

Dip data for lower α₋: p₋ ≤ 0 on [0, 0.887]; min p₋ = −0.100219 (bound −0.11 holds); at s = 3/4: p₋ = −0.0545 (note −0.0540), q₋ = 0.317, f₋ = −0.0556.

## Freeze recommendations
- T: hypotheses continuity of z_i, 0 < K. `crocco`: pressure sign as a parameter, export ψ′ = 1/q(ψ).
- A1/A1′: drop `hlim` or derive it. L: conclude p → 1 and f → ∞ (B = |f(a)| + 1). R: all real M.
- I, D, A2 as in the note; A2 with q(0) ∈ {1/2, 3/4} for better margins.
- B: split — q(0) < α₊ for every 𝓜 solution; α₋ < q(0) for every 𝓜 ∩ 𝓔 solution.
- B-existence and C: freeze only after the unclamping lemma is written.
