# Referee report: Blasius wall shear (frozen statements 4db71de)

Written by the run from the referee subagent's hand-back message (Sonnet, run 2026-11-07T1228Z): the subagent did not save its file; its scripts are not in the repository. Content as returned, condensed.

## 1. Statement attack
- hf, hp, hq say f' = p, p' = q, q' = −(f q/2) at every η ≥ 0, one-sided on Ici 0: exactly f''' + f f''/2 = 0 with q = f''; sign and factor 1/2 correct.
- f(0) = 0, p(0) = 0, p → 1 at atTop are exactly the Blasius conditions; no hypothesis vacuous or too strong. One-sided derivative at the wall is the right notion. Values on η < 0 are unconstrained and never enter the conclusion.
- p → 1 is the standard far-field condition; no boundedness, monotonicity or f'' > 0 is assumed (all derived), so the theorem is strong, not weak.
- Conclusion: σ = 0.33205733621519630 lies in [0.33205733621519, 0.33205733621520].
- Existence companion: same hypotheses under ∃, so the pair is non-vacuous once proved; classical (Töpfer, Weyl); its Lean proof needs global existence of the IVP (g'' = exp(−½∫g) > 0, g' bounded, monotone limit), then scaling.
- Cosmetic: cite Boyd's value as floating point only.

## 2. Proof plan, derived independently
- (a) correct; simpler alternative: q(t) = s·exp(−F(t)/2) with F = ∫₀ᵗ f, so q never vanishes unless s = 0; s = 0 ⇒ p ≡ 0, s < 0 ⇒ p ≤ 0, both contradict p → 1.
- (b) scaling correct: g(t) = f(t/c)/c, g''(0) = s/c³ = 1, g' → 1/c², s = α^{-3/2}.
- (d) correct: g'' > 0, g ≥ m = g(9) on [9, ∞), (g' + (2/m) g'')' = g''(1 − g/m) ≤ 0, so g'(9) ≤ α ≤ g'(9) + 2 g''(9)/m.
- (e) correct: s² = α^{-3}, monotone in α.
- (c) the real work: a validated enclosure of the IVP on [0, 9] to about 1e-14.

## 3. Independent numerics (mpmath, 50 digits, Taylor series, step 1/4, order 90)
- g(9) = 16.28370244619923024327, g'(9) = 2.085409176437902264243, g''(9) = 1.102562866671905e-14.
- α enclosure from t = 9 via (d): [2.0854091764379022642, 2.0854091764379036184], width 1.35e-15; continuing to t = 30: α = 2.085409176437903598067377.
- σ = α^{-3/2} = 0.3320573362151962989371801 (matches Boyd 0.33205733621519630).
- Margins: σ − lo = 6.30e-15, hi − σ = 3.70e-15.

## Verdict
STANDS. Statement faithful and non-vacuous (with the existence companion), proof plan correct. Suggestions (not blocking): integrating-factor argument for (a); state g'' → 0 explicitly in (d) (the program's proof does not need it: it bounds p(t) for each t ≥ 9 and passes to the limit p → 1/c²).
