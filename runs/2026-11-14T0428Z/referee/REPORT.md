# Referee report: run 2026-11-14T0428Z, `bonnor_ebert_min`

(Opus referee subagent; its final message, copied here by the run because subagents may not write report files. Scripts: `scripts/be_min.py`, `scripts/lyap.py`.)

Files read: only the brief and `runs/2026-11-14T0428Z/lean/BonnorEbertMin.lean`. Lean was not run.

## Verdict: STANDS

The statement is the right formalization of the claim. Every window contains the value computed independently, with room to spare. Not vacuous, not trivial. No corrections, only cosmetic notes.

## 1. Attack on the statement

- **Signs.** w = −ψ turns ψ'' + (2/ξ)ψ' = e^{−ψ} into w'' + (2/s)w' + e^w = 0, which is `hφ`. The contrast ρ_c/ρ = e^{−w} is correct.
- **Mass formula.** m = (4π)^{−1/2}(ρ_c/ρ_0)^{−1/2} ξ² ψ' = s²(−φ)e^{w/2}/√(4π), matching the Lean expression. In homology variables 4π m² = u v³; m' ∝ s² e^{w/2}(e^w − φ²/2), so critical points are where u = v/2.
- **Derivatives and continuity.** `hw` one-sided at 0 and S is fine; `hφ` only on (0, S], so the 2/s singularity is never evaluated. With `hφ0`, s²φ = −∫₀ˢ t²e^w dt, forcing φ(0) = 0; w then solves a Volterra equation with a Lipschitz kernel, so the hypotheses determine the Emden solution uniquely. `hφ0` is probably redundant. 
- **Non-vacuity.** The global Emden solution restricted to [0, S] satisfies every hypothesis.
- **Junk values.** None matter; m(0) = 0 is harmless in conjunct 1.
- **Role of S ≥ 150.** Equivalent to "every radius s ≥ ξ₁" (take S = max(150, s); by uniqueness the solution on [0, S] is the restriction of the global one). The bound does not weaken the statement.
- **"At least as centrally condensed."** φ < 0, so the contrast is strictly increasing in s; contrast ≥ contrast(ξ₁) ⇔ s ≥ ξ₁. The restriction to [ξ₁, S] is necessary (the minimum over [0, S] is m(0) = 0).
- **Quantifiers.** Conjunct 1 makes ξ₁ the unique strict maximiser on [0, S]; choosing ξ₁ and ξ₂ together does not weaken the ξ₂ conjunct; ξ₂ is the unique strict minimiser on [ξ₁, S].
- **Windows:**

| window | computed value | margin |
|---|---|---|
| ξ₁ ∈ [6.4507514, 6.4507515] | 6.450751444 | 4.4e-8 below, 5.6e-8 above |
| ξ₂ ∈ [67.0075, 67.0076] | 67.00754872 | ≈ 4.9e-5 below, 5.1e-5 above |
| m(ξ₂) ∈ [0.694366, 0.694367] | 0.6943665211 | ≈ 5e-7 each side |
| contrast ∈ [2579.69, 2579.71] | 2579.697330 | ≈ 0.007 below, 0.013 above |

- **Triviality.** None: strict global maximum, strict minimum over an unbounded range, enclosures to 6–7 digits.

## 2. Independent computation

Methods: A power series at 0 (80 terms) then mpmath `odefun` at 30 digits in t = log s, z = w + 2t (z'' + z' − 2 + e^z = 0); B scipy DOP853 in (w, φ), rtol 2.2e-14; C DOP853 in (u, v) against t = log ξ to ξ = 10⁷.

| quantity | A (mpmath) | B (DOP853) |
|---|---|---|
| ξ₁ | 6.45075144417407366 | 6.4507514441741 |
| m(ξ₁) | 1.18222658849959973 | 1.1822265884996 |
| contrast at ξ₁ | 14.0420320486407778 | 14.0420320486 |
| ξ₂ | 67.0075487195952397 | 67.0075487195923 |
| m(ξ₂) | 0.694366521128555379 | 0.6943665211285 |
| contrast at ξ₂ | 2579.69733045389228 | 2579.6973304537 |

Extrema (method C): max 6.4507514 (1.182226588500), min 67.007549 (0.694366521129), max 733.76924 (0.830690058276), min 7849.632 (0.787994187928), max 84506.329 (0.800911950079), min 907946.19 (0.796962175238), max 9760975 (0.798165990596); limit √(2/π) = 0.7978845608.

Smallest gap inf over {ξ ≥ ξ₁, |ξ − ξ₂| ≥ 1} of m(ξ) − m(ξ₂) ≈ 1.90e-5 (at ξ₂ + 1); away from that neighbourhood ≈ 0.0935.

Lyapunov tail: dV/dt = −(u−1)² ≤ 0. At ξ = 150: u = 1.05255554548, v = 1.86541942318, V(150) = 0.0060764306018 (A and C agree to 12 digits); m(150) = 0.737364664. Minimum of u v³ on {V ≤ V(150)}: 6.15963836277 at (0.95402655, 1.86207964); 4π m(ξ₂)² = 6.05881107175; margin 0.1008 (1.7%), so m ≥ 0.7001203 for every ξ ≥ 150.

## 3. Prior art (short: 3 searches, 3 fetches)

- First maximum (ξ ≈ 6.45, contrast 14.0, m ≈ 1.18) classical (Bonnor 1956, Ebert 1955). Chavanis, arXiv astro-ph/0207080 (UNVERIFIED, WebFetch, first 100k characters): only α = 6.45 / contrast 14.0 for the isobaric case, other ensembles' critical points, no mass minimum. Tohline/vistrails page (UNVERIFIED): first turning point only. arXiv 1511.03457: first 100k characters only, nothing relevant; rest not read.
- First minimum: nothing found in print for ξ₂ ≈ 67.0, m ≈ 0.6944 or contrast ≈ 2580 (may appear to 2–3 digits in older turning-point work — Chandrasekhar's tables, Lynden-Bell & Wood 1968, Katz 1978 — not verified).
- No interval or computer-assisted enclosure of any Bonnor–Ebert extremum found.
- "The first minimum is the smallest mass of the supercritical branch": no proof found; folklore from the damped spiral of (u, v) around (1, 2).

## 4. Verdict: STANDS

Cosmetic notes: the ξ₁ window is tight (≈ 4e-8 of room); `hφ0` probably redundant.

Sources: https://arxiv.org/pdf/astro-ph/0207080, https://vistrails.org/index.php/User:Tohline/SSC/Structure/BonnorEbert, https://arxiv.org/pdf/1511.03457
