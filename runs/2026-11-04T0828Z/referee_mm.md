# Referee report: Work/Sim/MichaelisMenten.lean (frozen)

**VERDICT: STANDS-WITH-CORRECTIONS** (the formal statements are correct and non-vacuous; the corrections are to docstring wording only)

Corrections:
1. The docstring says "first reaches half conversion". The theorem does not state this. It states p<1/2 on [0,2.5665] and p(2.5666)>1/2. "First crossing in (2.5665,2.5666)" is a corollary (IVT, continuity from HasDerivWithinAt). Either say "a crossing exists in (2.5665,2.5666) and none occurs before 2.5665", or add the IVT corollary as a theorem. Uniqueness of the crossing is not claimed, which is fine; p is monotone numerically, but the file does not prove it.
2. "QSSA is not reliable" is true but should be quantified or softened. The standard validity condition is e0 << s0+Km. Here e0 = 1 and s0+Km = 3, so the ratio is 1/3, which is not small. "Not reliable" is fair; "e0 = s0, so excess-substrate fails" is imprecise. The real reason is e0/(s0+Km) = 1/3 (see QSSA numbers below). Suggest rewording.
3. "Floating-point integration ... gives" is fine. Say that the reported value is 2.5665145299504 (the docstring has 2.566514530, which agrees).
4. Optional: note that the quantity certified is a statement about the exact ODE solutions. Uniqueness (Picard–Lindelöf / Gronwall, since the RHS is locally Lipschitz) is what makes "every solution" provable. The proof of claim 1 needs it, or needs a direct enclosure argument.

## 1. Independent numerics
Rate equations (derived from E+S⇌C→E+P, mass action): s'=-k1 e s + k-1 c, e'=-k1 e s + (k-1+k2)c, c'=k1 e s-(k-1+k2)c, p'=k2 c. Conservation gives e=1-c and s=1-c-p. The reduced system is c'=(1-c)(1-c-p)-2c, p'=c. The frozen file's equations match this exactly.

| Method | t½ |
|---|---|
| mpmath `odefun` (Taylor series), reduced 2-variable system, 40 digits, findroot at tol 1e-30 | 2.566514529950440200563015 |
| scipy DOP853, full 4-variable system, rtol 1e-13, atol 1e-15, dense output | 2.566514529950359 |
| scipy Radau, reduced 2-variable system, rtol 1e-13 | 2.566514529950436 |

- All three agree to about 12 digits: t½ = 2.5665145299504.
- t½ lies strictly in (2.5665, 2.5666). Margins: t½ − 2.5665 = 1.453e-5 and 2.5666 − t½ = 8.547e-5.
- p(2.5665) = 0.499997624630028, which is 2.375e-6 below 1/2.
- p(2.5666) = 0.500013972529881, which is 1.397e-5 above 1/2.
- p(13/5) = 0.5054488.
- On the grid [0, 2.6]: s, e, c, p ≥ 0, p is monotone, max c = 0.2344, min s = 0.3326, min e = 0.7656.
- The tightest margin is the lower bound at 2.5665, only 2.4e-6 in p. A validated enclosure must therefore be accurate to about 1e-6 in p there. That is easy for a Taylor/interval method, but the proof has to be genuinely tight (about 1e-7).
- Scripts: /tmp/claude-0/referee/a.py.

## 2. Attacks on the statement
- **Equations.** Signs and terms are correct. The expression `-k₁ * e t * s t` parses as (-k1)·e·s, which is fine. The system is redundant (4 equations, 2 conservation laws), but that is harmless and the docstring says so.
- **Derivative convention.** HasDerivWithinAt on Icc 0 T at each t is appropriate. It gives one-sided derivatives at the endpoints and implies continuity on [0,T] (ContinuousWithinAt). That suffices for IVT and for ODE uniqueness on [0,T]. It is a slight strengthening over an open-interval formulation, and it is not too weak, since it fixes the solution uniquely.
- **Junk values.** The functions are total ℝ→ℝ, but the statement only uses values in Icc 0 T. 25666/10000 ≤ 13/5, so p(2.5666) is inside the interval. No junk-value issue. Nothing depends on values outside [0,T].
- **Vacuity.** Claim 1 would be vacuous only if no solution existed, and one does. The RHS is polynomial, so a global solution exists. The bounded solution stays in [0,1], so there is no blow-up. Claim 2 states this existence. Proving it in Lean needs Picard–Lindelöf plus extension, or a constructive route such as a Taylor/series solution; this is non-trivial but standard. Uniqueness is not stated as a theorem but is implicit in claim 1.
- **Is T = 13/5 long enough?** Yes: t½ = 2.5665 < 2.5666 < 2.6, with a margin of 0.033. Note that T limits the interval on which the hypothesis is assumed; the hypothesis is stronger than needed. A smaller T would suffice, and T is not important to correctness.
- **QSSA comparison.** Briggs–Haldane: Km=(k-1+k2)/k1=2, Vmax=k2·e0=1. The integrated MM equation is Km·ln(s0/s)+(s0−s)=Vmax·t.
  - QSSA with p = s0−s (complex neglected): s=1/2 at t = 2ln2+0.5 = 1.88629. That is 0.680 below the true value, a 26% error.
  - QSSA with complex correction (p = 1−s−c, c = e0·s/(Km+s)): t = 2.74440, which is +0.178 above the true value, a 7% error.
  - Either way the difference is far larger than the 1e-4 certified window. The docstring claim that QSSA is "not reliable" is therefore supported, and the full-equation computation is necessary.

## 3. Prior art (from memory; no web search done, so treat as unverified)
- Isabelle/HOL: Immler et al., "Ordinary Differential Equations" (AFP) and the verified ODE solver / reachability work (Immler, Hölzl, Traut). It includes verified enclosures for the Lorenz system using Taylor models and affine arithmetic.
- Coq: Interval (Melquiond) and CoqInterval (verified approximations of integrals), plus Mahboubi–Melquiond–Sibut-Pinote on integrals. I do not recall a Coq verified ODE integrator at Isabelle's level.
- Lean 4/Mathlib: Picard–Lindelöf is available (`IsPicardLindelof`), but no verified interval ODE integrator. So the certificate here would need a new method (for example, Taylor enclosure with Gronwall-style a-posteriori bounds).
- Michaelis–Menten specifically: validated numerics for biochemical reaction networks exist (CAPD, INTLAB-based rigorous integration). I know of no certified (proof-assistant) interval solution of the full MM system. Treat that as likely novel, not confirmed.
