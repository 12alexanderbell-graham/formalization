# Prior art: Blasius wall shear sigma = f''(0)
READ (WebFetch): arXiv 1303.1416 (abs+pdf); arXiv 1212.5057 (pdf); Boyd 1999 Exp. Math. 8(4) project euclid page (abstract only).
SNIPPET ONLY (not read): arXiv math-ph/0203017, 1404.2248, 2003.07971/07730, 1104.5073, NASA NTRS items, Tanveer IUTAM talk.

## Q1 Rigorous enclosure
- Costin and Tanveer, "Analytical approximation of Blasius' similarity solution with rigorous error bounds", arXiv:1303.1416 (math.CA), 2013, preprint (journal not stated in what I read).
  Contraction-mapping + energy/Gronwall bounds; degree-12 polynomial on [0,5/2] + erfc form beyond. NOT interval arithmetic (polynomial max/min bounds, "convenient with a computer algebra program", rational arithmetic). Authors say bounds are likely ~10x overestimates.
  Printed: f''(0) = 0.469600 +/- 0.000022 in the f''' + f f'' = 0 normalization (a = lim F', f''(0)=a^(-3/2), their Eq. 6); footnote for Blasius variables: 0.3320574 +/- 0.000016, i.e. about 4 digits (interval approx [0.332041, 0.332073]).
- Classical analytic bounds (as quoted in 1212.5057, original not read): Callegari-Friedman 0.332055 < lambda < 0.33207; Blasius' own 1908 bounds 0.3315 < lambda < 0.33175 are reported as wrong. Weyl 1942 shows f'' > 0, decreasing to 0.
- No other validated-numerics/interval (e.g. Arb, INTLAB, Taylor models) result found in my searches; absence is not proof. Best published rigorous: about 4-5 digits.
- Floating-point only: Boyd 1999 "The Blasius function in the complex plane", Exp. Math. 8:381-394 (euclid 1047262359): "at least eleven digits" (abstract); 1212.5057 cites Boyd as 0.33205733621519630 (17 s.f.), Fazio 0.332057336215 (12 d.p.), Toepfer 1912 0.33206.

## Q2 Machine-checked proofs
Searches (Lean/Coq/Isabelle/HOL + Blasius) returned no formalization. Not found (searched only through web search, so inconclusive but likely none).

## Q3 Derivation (checked by me)
- f''' = -(1/2) f f''. Linear ODE for f'' given f: f''(x) = s exp(-(1/2) int_0^x f). So f''(0)=0 would force f'' = 0, f = 0, contradicting f'(inf)=1; hence s != 0. If s<0, f''<0 as long as it exists, f' decreasing from 0 so f' < 0 and f <= 0 for x>0, contradicting f'(inf)=1. So s>0. (Also f'' > 0, f' increasing, f' < 1 follows.)
- Scaling: c = s^(1/3), g(t) = f(t/c)/c. g' = f'(t/c)/c^2, g'' = f''(t/c)/c^3, g''' = f'''(t/c)/c^4; g g'' = f f''/c^4 so g''' + g g''/2 = 0. OK. g(0)=g'(0)=0, g''(0)=s/c^3=1. g'(inf) = 1/c^2 = s^(-2/3) =: alpha. So s = alpha^(-3/2). CONFIRMED. (Matches Costin-Tanveer Eq. 6 up to normalization.)
- Reverse: the IVP g''(0)=1 has a global solution (g'' = exp(-(1/2) int g) stays positive, g' bounded, limit alpha exists, finite, alpha > 0), so existence of the BVP solution = IVP + scaling; uniqueness = alpha determined by IVP, s unique given by the formula. This is the Toepfer 1912 reduction.
- Uniqueness/existence in print: Weyl 1942, Ann. Math. 43:381-407 (existence, uniqueness, f''>0 decreasing to 0), Toepfer 1912, Z. Math. Phys. 60:397-398 (scaling reduction, 5-digit value; refs per 1212.5057, originals not read). Qualitative answer yes in print.

## Q4 Agreement check
- Program: alpha = 2.08540917643790359..., sigma = 0.33205733621519629894.
- Recomputed (mpmath, 30 dps): alpha^(-3/2) = 0.33205733621519630086; sigma^(-2/3) = 2.085409176437903598055. Program's alpha agrees to all printed digits; the sigma difference (about 2e-18) is the truncation of the quoted alpha. Self-consistent.
- Agrees with Boyd's 0.33205733621519630 (17 s.f.) as cited in 1212.5057 (that is the only high-precision literature value I saw; I did not read Boyd's full text, so Boyd's own digit count, and any 20-digit values in the literature, are unverified). Rounds consistently with Fazio 0.332057336215, Costin-Tanveer interval, Callegari-Friedman bounds.

## Verdict
Novelty: a rigorous enclosure beyond ~4 digits (Costin-Tanveer 2013) and any formal proof appear unpublished per this screen; beyond 17 digits no published (float) value was seen.
rigorous enclosure in print: yes (digits: ~4, 0.3320574 +/- 1.6e-5, Costin-Tanveer arXiv:1303.1416; classical 0.332055<sigma<0.33207; no interval-arithmetic or formal result found)
