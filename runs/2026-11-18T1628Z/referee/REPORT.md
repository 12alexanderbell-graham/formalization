# Referee report: `bonnor_ebert_count` (run 2026-11-18T1628Z)

(Opus subagent, brief `BRIEF.md` in this folder; its file write was refused by the tool, so the main session saved the report from its final message. Script: `scripts/be_count.py`. Lean not run.)

**Verdict: STANDS.** The statement is a faithful formalization of the claim. Every conjunct is true. The existential sequence is uniquely pinned. The bands cover every μ > 0. The planned route works, with two points to check (R1, R2); neither is a defect in the statement.

## 1. Attack on the statement

- **Solution class.** w differentiable within [0,∞) with derivative φ, φ continuous at 0, φ' = −(2/s)φ − e^w on (0,∞), w(0) = 0. From (s²φ)' = −s²e^w and φ bounded near 0, s²φ(s) = −∫₀ˢ t²e^w dt, so φ(0) = 0 is forced: exactly the regular isothermal solution. Non-empty (the global solution exists); not too wide (integral-equation uniqueness). Values at s < 0 never enter (`Ici 0`); at interior points `HasDerivWithinAt … (Ici 0)` is `HasDerivAt`.
- **Parsing.** m parses as intended, the ODE right-hand side is correct, decimal literals are exact rationals, the casts `((2*k+2 : ℕ) : ℕ∞)` are fine, `encard = ⊤` is "infinite".
- **Normalisation.** The singular sphere has m = (1/√4π)·ξ²·(2/ξ)·(√2/ξ) = √(2/π), matching the limit clause; m(ξ₀) ≈ 1.18 is the standard Bonnor–Ebert critical mass M G^{3/2} P^{1/2} / c_s⁴.
- **Junk values.** m(0) = 0, so s = 0 never counts for μ > 0. Nothing is claimed for μ ≤ 0 (N(0) = 1, N(μ < 0) = 0); harmless. N(m(ξ₀)) = 1 needs no positivity hypothesis.
- **Each conjunct is true** (by hand from the given facts; the even values decrease, the odd values increase, both strictly on either side of √(2/π)):
  - (m₂ₖ₊₂, m₂ₖ): one root on [0, ξ₀] and one on each [ξ_j, ξ_{j+1}], j = 0 … 2k: 2k+2; none for s ≥ ξ₂ₖ₊₁ (m ≤ m₂ₖ₊₂ < μ).
  - μ = m₂ₖ₊₂: the same plus ξ₂ₖ₊₂: 2k+3.
  - (0, m₁): one root (m ≥ m₁ > μ for s ≥ ξ₀).
  - μ = m₂ₖ₊₁: 1 + 2k + 1 = 2k+2.
  - (m₂ₖ₊₁, m₂ₖ₊₃): 1 + (2k+1) + 1 = 2k+3; none on [ξ₂ₖ₊₂, ∞) (m > m₂ₖ₊₃ > μ).
  - μ = √(2/π): one root per segment, N = ⊤.
- **Coverage.** (m₂ₖ₊₂, m₂ₖ] give (√(2/π), m₀]; (0, m₁) and [m₂ₖ₊₁, m₂ₖ₊₃) give (0, √(2/π)); with (m₀, ∞) and √(2/π) every μ > 0 is covered (uses the limit clause).
- **ξ is pinned uniquely.** For any ξ′ satisfying the conclusion, aₖ = m(ξ′ₖ): N = 0 above a₀ and N(a₀) = 1 force a₀ = m₀ (so ξ′₀ = ξ₀, strict global maximiser); N = 1 on (0, a₁) and N(a₁) = 2 force a₁ = m₁; N = 2 on (a₂, m₀) and N(a₂) = 3 force a₂ = m₂ (a₂ ≤ √(2/π) would put √(2/π), where N = ⊤, in the band); induction gives aₖ = mₖ, and strict monotonicity with the strict-extremum facts gives ξ′ₖ = ξₖ. The existential does not weaken the statement.
- **Radii = spheres.** With T, P_ext, M fixed, μ is fixed; a sphere is the solution cut at s > 0 with ρ_c = P e^{−w(s)}/c_s², R = s c_s/√(4πGρ_c). w is strictly decreasing on (0,∞) (φ < 0), so distinct radii give distinct spheres. The count includes unstable equilibria (correct for "number of equilibria").

## 2. Planned route

Sound. Points to watch:

- **R1 (identification).** If rₖ is the strict extremiser on [ξₖ₋₁, S] and ξₖ the strict extremiser on [ξₖ₋₁, ∞): ξₖ ≤ S gives rₖ = ξₖ; ξₖ > S makes m strictly monotone on [ξₖ₋₁, S], so rₖ = S. So the step needs rₖ < S: each certified lemma's S must exceed its radius window (6.45, 67.0076, 734, 7849.75, 84516). The predecessor must be identified first (induction on k).
- **R2 (counting).** The counting lemma as written covers the open bands; the band-end clauses need a variant (segments strictly up to ξ_{N−1}, then the single endpoint root ξ_N; the tail fact for s ≥ ξ_{N−1}, s ≠ ξ_N excludes the rest), and the ⊤ clause an infinite variant (one root per segment, injective in the index because open segments are disjoint). Continuity of m on [0,∞) holds.
- The ξ₀ window and the limit come directly from the monotone headline. No other gap.

## 3. Independent computation

Log variables t = ln s, u = w + 2t: u′ = v, v′ = 2 − v − eᵘ, m = (2 − v) e^{u/2}/√(4π); extrema of m at eᵘ = (2 − v)²/2. DOP853 at rtol 1e-13, cross-checked at 1e-11 (differences ≤ 7e-12); an s-form integration agrees to 10 digits for k ≤ 4.

| k | ξₖ | m(ξₖ) | window |
|---|---|---|---|
| 0 | 6.450751444 | 1.1822265885 | ✓ (ξ₀ window ✓) |
| 1 | 67.00754872 | 0.6943665211 | ✓ |
| 2 | 733.7692437 | 0.8306900583 | ✓ |
| 3 | 7849.632049 | 0.7879941879 | ✓ |
| 4 | 84506.32898 | 0.8009119501 | ✓ (1.95e-6 above the lower end) |
| 5 | 907946.1932 | 0.7969621752 | — |
| 6 | 9.760975e6 | 0.7981659906 | — |
| 7 | 1.049170e8 | 0.7977987305 | — |

√(2/π) = 0.7978845608; |mₖ − √(2/π)| shrinks by about ×0.30 per extremum.

N(μ) as sign changes of m − μ on 4·10⁶ grid points in t, s ∈ [1e-3, 1e13], against the segment count from the extremum values (agree; both match the band formula):

| μ | 0.5 | 0.7 | 0.75 | 0.79 | 0.7975 | 0.80 | 0.81 | 0.9 | 1.18 | 1.19 |
|---|---|---|---|---|---|---|---|---|---|---|
| N | 1 | 3 | 3 | 5 | 7 | 6 | 4 | 2 | 2 | 0 |
| band | (0,m₁) | (m₁,m₃) | (m₁,m₃) | (m₃,m₅) | (m₅,m₇) | (m₆,m₄) | (m₄,m₂) | (m₂,m₀) | (m₂,m₀) | > m₀ |

## 4. Prior art (brief)

Classical picture; exact band-by-band count not found stated as a theorem in what was read.

- Ebert 1955 (Z. Astrophys. 37, 217), Bonnor 1956 (MNRAS 116, 351), Chandrasekhar 1939 ch. IV: not read.
- Chavanis, arXiv:astro-ph/0207080 (WebFetch, UNVERIFIED): credits Ebert, Bonnor, McCrea with the critical pressure; P_max = 1.40 k⁴T⁴/(G³M²m⁴), α = 6.45, contrast 14.0 (consistent with m₀² ≈ 1.3977); P–V spiral; no explicit count in the part read.
- Giordano et al., arXiv:1903.04044 (WebFetch, UNVERIFIED): box parametrisation; multiple solutions beyond a threshold, infinitely many at the spiral-centre value.
- Lombardi & Bertin 2001, arXiv:astro-ph/0106336: abstract only, no count.

## 5. Verdict

**STANDS.** Correct, well posed, not vacuous, existential uniquely determined, windows confirmed independently. For the proof: R1 and R2.
