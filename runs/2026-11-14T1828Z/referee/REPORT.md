# Referee report: run 2026-11-14T1828Z, `bonnor_ebert_third_max` (BonnorEbertMax3.lean)

(Opus subagent, brief `BRIEF.md`; the subagent could not write files, so its final message is copied here by the run, unedited in substance. Scripts copied from its temp dir to `scripts/`.)

**Verdict: STANDS.** The statement correctly formalizes the headline. It is not vacuous and not trivial. Every window contains the true value, and two independent high-precision methods agree to at least 13 significant digits. No corrections are needed.

## 1. Attack on the statement
- ODE and signs correct: ψ'' + (2/ξ)ψ' = e^{−ψ} with w = −ψ gives w'' + (2/s)w' + e^w = 0; with φ = w', φ' = −(2/s)φ − e^w, exactly `hφ`. Contrast ρ_c/ρ(R) = e^{ψ} = e^{−w}.
- Mass formula correct: m = (4π)^{−1/2} ξ² ψ' e^{−ψ/2} = ξ²(−φ)e^{w/2}/√(4π); reproduces the first maximum 1.18223 and the limit √(2/π) = 0.797885. √(4π) > 0, no junk values.
- Hypotheses force the regular solution: continuity of φ at 0 makes s²φ(s) → 0; (s²φ)' = −s²e^w gives φ(0) = 0; with w(0) = 0 the integral equation is a contraction near 0 and the ODE Lipschitz on (0, S].
- Not vacuous: the global solution exists and its restriction to [0, S] satisfies the hypotheses for every S.
- S ≥ 300000: for any radius s ≥ ξ₄ apply the theorem with S = max(s, 300000); each ξᵢ is forced (strict extremiser on a set containing it), so "every S ≥ 300000" is equivalent to "every radius ≥ ξ₄". Any S < ξ₅ would make the statement false.
- Quantifiers fine (ξ₁ … ξ₅ chosen together; unique). "At least as centrally condensed" = s ≥ ξ₄ since e^{−w} is strictly increasing.
- Literals, docstring and header agree.

## 2. Independent computation
Method A: scipy DOP853 float64, rtol 1e-13, start ξ = 0.1 from the power series. Method B: own order-30 Taylor integrator in mpmath (40 digits step 0.05 and 60 digits step 0.025, agree to 20 digits). A and B agree to 12–13 significant digits. Variables t = log ξ, z = w + 2t, y = ξw'; extrema of m where v = 2u.

| extremum | ξ | m(ξ) | e^{−w(ξ)} |
|---|---|---|---|
| max ξ₁ | 6.4507514441740736585 | 1.1822265884995997255 | 14.042032048640777763 |
| min ξ₂ | 67.007548719595239719 | 0.69436652112855537885 | 2579.6973304538922809 |
| max ξ₃ | 733.76924368659781205 | 0.83069005827551933842 | 258577.1004705434705 |
| min ξ₄ | 7849.6320485004269309 | 0.78799418792767269718 | 31195047.475608645634 |
| **max ξ₅** | **84506.328975744925839** | **0.8009119500784999699** | **3557162982.4774751869** |
| min ξ₆ | 907946.19315370931809 | 0.79696217523850253069 | 4.1266019605702e11 |
| max ξ₇ | 9760974.9810400211657 | 0.79816599059605466867 | 4.7621519230912e13 |

Windows: ξ₅ ∈ [84497, 84516] ✓; m ∈ [0.80091, 0.800916] ✓ (margins 1.95e-6 / 4.05e-6); contrast ∈ [3556300000, 3558000000] ✓ (margins ≈ 8.6e5 / 8.4e5).
- m(10⁷) = 0.79816582714247; damped oscillation about √(2/π); deviation shrinks by ≈ 3.3 per half-turn.
- sup{m(ξ) : ξ ≥ ξ₄, |ξ − ξ₅| ≥ 1} at ξ₅ ± 1, 4.26e-13 below m(ξ₅) (strict but flat maximum).
- Volterra: V(300000) = 3.045731253e-6 (u = 0.998005548042, v = 2.002054152079); max of u v³ on {V ≤ V₀} = 8.0464282142278 (at u* = 1.001052916877, v* = 3u* − 1) < 4π m(ξ₅)² = 8.0608234883182; margin 0.0144.

## 3. Prior art
- WebSearch, three queries: no numbers for the third maximum, no rigorous enclosure.
- Tohline, VistrailsWiki "SSC/Structure/BonnorEbert" (WebFetch, UNVERIFIED): only the first critical point.
- arxiv.org/pdf/astro-ph/0207080, Chavanis 2003 (WebFetch, UNVERIFIED, first 100k characters): first critical points only, no later extrema.
- arxiv.org/pdf/astro-ph/0103159 (Chavanis 2002): not read (permission timed out).
- Conclusion: in what could be read, position, value and contrast of the third maximum are not in print; no rigorous enclosure; no proof that it is the largest mass beyond the second minimum. The damped spiral and oscillation about √(2/π) are classical (Chandrasekhar 1939; Bonnor 1956; background knowledge, not verified). Short search: Emden's, Chandrasekhar's and Horedt's tables not checked.

## 4. Verdict: STANDS
