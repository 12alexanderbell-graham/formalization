# Referee + prior-art report (run 2026-11-11T0232Z)

Written by the referee subagent (Opus); its own Write call was refused by the harness ("subagents should return findings as text"), so the main session saved its final message here verbatim in substance (lightly reformatted). Scripts: `scripts/beta_star_odefun.py`, `scripts/dop853_check.py`, `scripts/wall_shear_check.py`; logs were kept outside the repository.

**Verdict: STANDS.** `fs_separation_exists` correctly formalizes existence of the zero-wall-shear separation profile (Hartree's profile) and is true. Non-blocking correction: the theorem is existence only; call it "the separation value lies in the window" only once a uniqueness-in-β theorem (§1.3) is frozen and proved.

## 1. Attack on the statement
### 1.1
- Derivatives one-sided (`HasDerivWithinAt … (Ici 0)`); values for η < 0 unconstrained (harmless). No division, sInf or casts; window literals in the right order. No junk-value loopholes.
- The sign of β is forced: q'(0) = −β; β > 0 gives q < 0 just right of 0, contradicting q > 0 on (0, ∞); β = 0 with start (0, 0, 0) gives f ≡ 0, contradicting p → 1.
- q > 0 on (0, ∞) is not too strong: q'(0) = −β > 0; at a zero of q with |p| < 1, q' = −β(1 − p²) > 0; p never touches 1.
- The decay condition excludes the algebraic solutions: for β* < β < 0 the zero-shear shot reaches p → 1 with 1 − p ~ C η^{2β}, q/(1 − p) ~ 2|β|/η → 0, so "eventually M(1 − p) ≤ q" fails for every M > 0. Without it every β in the window would satisfy the statement. The separation profile passes (Gaussian tail: q/(1 − p) = D_{ν+1}(x)/D_ν(x) ~ x; measured 9.70 at x = 9.64).
- β < β* excluded: the zero-shear shot overshoots (p > 1), and with q > 0 p is increasing, so p → 1 is impossible.
- Nothing missing: f' ≤ 1 follows from p increasing to 1. Matches Hartree's definition (f''(0) = 0, 0 < f' < 1, f' → 1 exponentially fast).
### 1.2 Existence-only form
The theorem says S = {β : a zero-shear solution with p → 1, q > 0 and the decay condition exists} meets the window. S is a single point by §1.3, so the statement is equivalent to β* ∈ window — but that is a separate theorem. Honest wording until then: "a separation profile (zero wall shear, Gaussian tail) exists with β ∈ (−0.1988377351, −0.1988377350)".
### 1.3 Provable uniqueness
**Theorem.** β₁ < β₂; if the β₂ problem has a zero-shear solution with p → 1, q > 0 and the decay condition, the β₁ problem has no zero-shear solution with p → 1 and q > 0 (even without decay). **Corollary (Lean):** two separation solutions (nine conjuncts of the frozen statement each) have β₁ = β₂.
Route (Crocco variables, unscaled β-form, adapting Theorem U′, research note 2026-11-09T0428Z §2):
1. t = f', z(t) = f'', F(t) = f on (0, L), L < 1: z' = −F + |β|(1 − t²)/z, F' = t/z, ψ' = 1/z (ψ(t) = the η with f' = t).
2. Start (the only new step): q = |β|η + O(η²), p = |β|η²/2 + O(η³) ⇒ z_i(t)/√t → √(2|β_i|); |β₁| > |β₂| ⇒ z₁ > z₂ near t = 0; 1/z ~ t^{−1/2} integrable, so ψ, F extend continuously to t = 0.
3. No crossing: D = z₁ − z₂, E = F₂ − F₁; while D > 0, E' = t(1/z₂ − 1/z₁) > 0; at a first zero t*, D'(t*) = E(t*) + (|β₁| − |β₂|)(1 − t*²)/z > 0, impossible. So D > 0, E increasing.
4. Ψ = D + 2|β₂|G₂ − E(t₀)s, G₂ = ψ₂ − F₂, G₂' = (1 − t)/z₂; with 1 − s² ≤ 2(1 − s), Ψ' ≥ 0 for s ≥ t₀: E(t₀)(t − t₀) ≤ D(t) + 2|β₂|(G₂(t) − G₂(t₀)).
5. Decay of solution 2 with constant M: G₂(t) − G₂(t₀) ≤ (t − t₀)/M (χ = x − f₂ − p₂/M non-increasing).
6. M = 4|β₂|/E*; a level t near 1 with z₁(t) < ε (p₁ → 1, ∫q₁ < ∞) gives D(t) < ε, contradicting step 4 (Step 3 of U′ essentially unchanged).
Not recommended: monotonicity of the attached branch's wall shear in β (Coppel 1960; needs the whole branch); comparison in the scaled K form (same leading term at the start, step 2 loses strictness).

## 2. Independent computation
Unscaled β-form shot from (0, 0, 0), `mpmath.odefun` at 45 digits, matched at η∞ to the decaying mode of the linearised tail g = 1 − f' = e^{−x²/4} D_ν(x), ν = −1 − 2β (−g'/g = D_{ν+1}/D_ν, `mpmath.pcfd`), secant on β.

| η∞ | β* |
|---|---|
| 7 | −0.198837735046785… |
| 8 | −0.19883773504667754911 |
| 9 | −0.198837735046677546889053… |
| 10 | −0.198837735046677546889047131818… |
| 11 | −0.19883773504667754688904713181526305457 |
| 12 | −0.19883773504667754688904713181526305439 |

β* = −0.198837735046677546889047131815263054 (≈ 35 stable digits); scipy DOP853 + `pbdv`: −0.198837735046679 (14 digits). Agrees with the run's value in all 20 printed digits. **β* ∈ (−0.1988377351, −0.1988377350): yes**, margins 5.33·10⁻¹¹ and 4.67·10⁻¹¹. K* = 5.0292264683323215571…, m* = β*/(2 − β*) = −0.0904285622706291…, δ = lim(η − f) = 2.35884627657….

Wall shear f''(0): β = −0.1988: upper 0.00521818788391, lower −0.00515742017793; β = −0.198837723795: ±8.96·10⁻⁵; β = −0.19: 0.08569974406 / −0.07133590600; β = −0.1: 0.319269759843 / −0.140546213 (reproduces the 2026-11-09 note). (β − β*)/α² → ≈ 1.40: the attached and Stewartson branches meet in a fold at β*.

## 3. Prior art (quotes from WebFetch summaries; arXiv via arxiv.org/pdf only)
| Source | Printed value | Agrees? |
|---|---|---|
| Stewartson 1954, Proc. Camb. Phil. Soc. 50 (abstract) | "when β < −0·1988 there are no solutions satisfying \|f′\| ⩽ 1" | yes, 4 digits |
| Hartree 1937 via Asaithambi, Fluids 6 (2021) 153 | "−0.198838 ≤ β ≤ 4/3" | yes, 6 digits |
| Hartree via Zhu–Cheng–Wu preprint (2009) | "−0.19884 < γ < 0" | yes |
| Univ. of Iowa (Stern) lecture notes Ch. 4 | "−0.19884 ≤ β ≤ 1.0" | yes |
| Wazzan, Okamura & Smith 1968 (DTIC AD0712198) | "β = −0.1988 (separation)", δ* 2.359 | yes |
| Barlow et al., arXiv:1907.09912 (2019) | "(−0.198837735, 0, −2.359)" | **yes, 9 digits correctly rounded** (most precise correct printed value found) |
| Fazio, arXiv:2011.07725 (2020) | Fig. 7 caption "β = −0.1988376" with f''(0) = 0 | **no**: true value rounds to −0.1988377 (off 1.35·10⁻⁷) |
| Fazio, arXiv:1212.5057 (2012) | "β = −0.198837723795 … skin-friction coefficients 6.61D−06 and −6.61D−06" | **no**: true wall shears there ±8.96·10⁻⁵; implied β* wrong from the 8th digit |

Printed f''(0) at β = −0.1988 (Asaithambi 0.005225, Zhang 0.005222, Salama 0.005226, Zhu 0.005229) are 0.07–0.21 % above the true 0.0052182 (4th digit wrong; consistent with truncation at η∞ ≈ 7). "−0.19883768": no printed occurrence found.
Not read (failed/timed out, not refetched): Wikipedia Falkner–Skan page; Caltech record of Cebeci–Keller 1971; Ganapol arXiv:1006.3888 tables; full texts of Hartree 1937, Smith 1954, Stewartson 1954, Cebeci–Keller, Rosenhead, White, Veldman–van de Vooren.
UNVERIFIED (memory): White's table −0.19884; Smith 1954 ≈ 5–6 digits; Coppel 1960 / Hartman 1972 characterise β* as the infimum of β for monotone attached solutions; f''(0) increasing in β credited to Coppel in Asaithambi 2021.
**No rigorous or computer-assisted enclosure of β* found** (limited search: absence of evidence). Scalings: m-convention β = 2m/(m+1), m* = −0.09042856227…; no mapping onto another tabulated family known.

## 4. Verdict
**STANDS.** β < 0 is forced; the decay condition excludes the algebraic profiles; two independent methods put β* ≈ 5·10⁻¹¹ inside each window end; prior art agrees wherever it claims correctly rounded digits, except Fazio's truncated-domain values (2012, 2020), wrong in the 7th–8th digit. Non-blocking: do not headline "β* ∈ window" until `fs_separation_unique` is proved.
