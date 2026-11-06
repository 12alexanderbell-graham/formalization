# SRK acentric blind notes
- kappa, aT (kappa 1 inside), P, IsCritical, IsMaxwell defined in Blind.SRKAcentric; R, ac, b, Tc as free reals.
- Hyps: R>0, ac>0, b>0, Tc>0 (needed for sqrt(T/Tc), sign of terms); IsCritical gives vc>b plus deriv/deriv-deriv = 0 of v ↦ P v Tc at vc.
- Critical conditions pin down vc = b/(2^(1/3)-1) and ac in terms of R Tc, b, so no extra hypotheses; result is scale-free.
- Junk avoided: v>b>0 on all evaluated points so no x/0; P is smooth on (b,∞) so `deriv` at vc>b is the true derivative
  (the second `deriv (deriv f)` is also true since f is smooth near vc); integrand is continuous on [vl,vg] ⊂ (b,∞) so the interval integral is real, not 0-junk.
- Real.logb 10 of ps/Pc: no positivity hyp; the first RoundsTo (ps/Pc≈0.0102) forces positivity, so log is not junk in a true instance. (Pc>0 is not assumed; it follows.)
- Pc = P vc Tc (a(Tc)=ac since sqrt 1 = 1).
- Numerics (mpmath, 40 digits, R=Tc=b=1): vc=3.84732 b, ac=4.93396, kappa(1)=1.878, Pc from these.
  Maxwell solve at T=0.7Tc: vl=1.22695 b, vg=782.08 b, ps/Pc=0.0101851, omega_out=0.992034.
  Rounds: 0.0102 (4 dp) OK, 0.992 (3 dp) OK. Existence: root found.
- Uniqueness only spot-checked (coarse grid scan, one sign change per branch); not rigorously proven numerically.
- Not compiled.
