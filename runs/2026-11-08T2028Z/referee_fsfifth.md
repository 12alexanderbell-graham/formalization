# Referee: Work/FalknerSkan/FifthBounded.lean (FS beta = 1/5, class -1 <= f' <= 1)

VERDICT: STANDS

## 1. Statement attack
- ODE: f'=p, p'=q, q' = -(f q) - (1/5)(1-p^2) is exactly f''' = -f f'' - beta(1-f'^2) at beta=1/5. Sign and coefficient correct.
- Quantifiers: all three theorems quantify over f p q : R -> R with derivative hypotheses only on Ici 0 (HasDerivWithinAt within Ici 0, one-sided at 0). Values off [0,inf) are junk but never constrained or used; conclusions of `equal` are restricted to Ici 0. No junk-value leak.
- Boundary data f(0)=0, p(0)=0, Tendsto p atTop (nhds 1) match f(0)=f'(0)=0, f'->1. q(0) is not assumed positive, which is the right (weaker-hypothesis, stronger-theorem) choice.
- Class: -1<=p<=1 is a closed, weaker-than-"0<f'<1" class (Hartree/Stewartson normal-flow restriction), so window/uniqueness are stronger than the textbook-restricted statement. Printed theory (Coppel, Craven-Peletier) removes the restriction entirely for 0<=beta<=1, so the class is sensible and true. Not too weak (reverse-flow solutions with p<-1 or p>1 excluded; at beta=1/5 none are known anyway).
- Existence: conclusion 0<=p<1 matches the physical profile (p'=q>0); strictness p<1 is correct (p approaches 1 exponentially, never reaches it). Not vacuous: numerics below exhibit the solution. The three theorems are consistent (existence's solution is in the bounded class, hence equal/window apply).
- Window 0.6867081809 < q0 < 0.6867081811: width 2e-10, true value inside with margins 1.3e-10 (low) and 6.8e-11 (high). Decimal literals are exact rationals in Lean (OfScientific on R), no float issue.
- Minor remarks (no correction needed): the doc comment says "wedge half-angle pi/10"; for beta=2m/(m+1)=1/5, m=1/9, wedge angle beta*pi = pi/5 total (half-angle pi/10). Consistent.
- Scaling lemma (FSScale.scale) read: takes a, b, c>0, gives (c f(s/c), p(s/c), q(s/c)/c) solving the system with a/c^2, b/c^2, same limit of p (scale_lim). With a=1, b=1/5, c^2=1/5: coefficients 5 and 1. F''' + 5 F F'' + 1 - F'^2 = 0 as planned. Bound class and p-range preserved since p(s/c) has the same range.

## 2. Independent computation (mpmath 30 digits, odefun Taylor, Newton on p(L)=1, L = 6..14)
- beta=1/5, f''' + f f'' + (1-f'^2)/5 = 0:
  f''(0) = 0.686708181032193672040012466 (L=12, L=14 agree to 1e-29; L=10 agrees to 1e-13; L=8 to 4e-11)
  Window (0.6867081809, 0.6867081811): INSIDE strictly.
- Scaled, F''' + 5 F F'' + 1 - F'^2 = 0, F(0)=F'(0)=0, F'->1:
  F''(0) = 1.53552617349321674943048808647 (L=6,8,10 identical). sqrt5 * f''(0) = 1.53552617349321674943048808649, agrees with F''(0) to 2e-29 (the rest is shooting tolerance).
  Window (1.5355261734, 1.5355261735): INSIDE strictly (margins 9.3e-11 low, 6.8e-11 high... i.e. 1.5355261734932).
- Transfer: sqrt5*0.6867081809 = 1.5355261731976 < 1.5355261734 (ok); sqrt5*0.6867081811 = 1.5355261736448 > 1.5355261735 (ok). So the F-window (1.5355261734, 1.5355261735) sits strictly inside sqrt5*(0.6867081809, 0.6867081811); the transfer F-window => f-window works, with slack ~2.0e-10 / 1.4e-10 on the two sides (dividing by sqrt5 needs sqrt5 bounds of ~1e-11 relative accuracy; FSScale rational sqrt 2 bounds are for the Homann row, a sqrt 5 bound is needed here and is not in FSScale).
- Warning for the prover: a naive float64 shooting with escape threshold p>1+1e-7 gave 0.6867081953 (outside the window); that is a threshold artefact, not a counterexample. High-precision with exact p(L)=1 conditions is the reliable check. Certified shooting events must use exact comparisons, not tolerances.

## 3. Prior art
Read: arxiv.org/pdf/2011.07725 (Iterative Transformation Method, existence/uniqueness survey). It reports: Hartree/Stewartson unique solution for beta>0 under 0<f'<1; Coppel and Craven-Peletier: restriction dropped for 0<=beta<=1; Weyl: physical solution with q>0 decreasing to 0 exists for each beta; Craven-Peletier: uniqueness lost for beta>1; Veldman-van de Vooren: multiplicity for beta_min<beta<0. No value at beta=0.2 there.
Not read (only search-result titles seen, nothing fetched): Weyl 1942, Coppel 1960, Craven-Peletier 1972 originals, Hastings papers, Springer BF00944877/BF00039325, arXiv 1907.09912, 2008.01671, 1008.2322, Caltech Appendix B, any high-precision beta=0.2 table. Hastings not mentioned in the one document read.
Conclusion: the qualitative answer (existence + uniqueness at beta=1/5, even without the f'<1 restriction, and unbounded-class uniqueness) is already in print via Weyl/Coppel/Craven-Peletier. The 10-digit rigorous enclosure of f''(0) and a machine-checked proof of it is the new content; I did not find a published 12+ digit value at beta=0.2 (not verified: those sources not read). Classical tables 0.686708 agree with my 0.6867081810.

## Summary for caller
1. STANDS: ODE form, quantifiers, one-sided derivatives, boundary data, and bounded class are faithful and non-vacuous; no junk-value leak.
2. f''(0)=0.68670818103219367204 (30-digit mpmath shooting), strictly inside (0.6867081809, 0.6867081811).
3. F''(0)=1.5355261734932167494 in (1.5355261734, 1.5355261735); sqrt5-transfer inequalities both hold (1.5355261731976 < 1.5355261734; 1.5355261735 < 1.5355261736448).
4. FSScale.scale with a=1,b=1/5,c^2=1/5 gives coefficients 5 and 1 as claimed; a sqrt 5 rational bound (relative 1e-11) will be needed, FSScale has only sqrt 2.
5. Existence/uniqueness for 0<=beta<=1 is classical (Weyl, Coppel, Craven-Peletier; confirmed via one arXiv survey only); the novelty is the certified window. Beware float-threshold shooting artefacts.
