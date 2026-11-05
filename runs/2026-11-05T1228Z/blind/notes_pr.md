# PR blind restatement notes
- kappa defined as function, evaluated at omega=1 (kappa 1 = 1.64698); a(T) uses sqrt(T/Tc) with Tc a parameter.
- Hypotheses: R>0, b>0, ac>0 only; critical point = Tc>0, vc>b, deriv and deriv∘deriv of isotherm at Tc vanish, Pc = P(vc,Tc).
- Isotherm v ↦ P(v,Tc) smooth near vc>b (denominator v^2+2bv-b^2 > 2b^2), so deriv is genuine.
- Coexistence: b<vl<vg, equal pressures ps, interval integral = ps*(vg-vl).
- ps/Pc rounds to 0.0114 at k=4; acentric = -logb 10 (ps/Pc) - 1 rounds to 0.942 at k=3; 0<ps/Pc stated to avoid log junk.
- "Does not reproduce input": acentric ≠ 1.
- Existence of critical point not assumed beyond hypothesis hc (universal over critical points).
Sanity (mpmath, b=R=Tc=1): ac=5.8774, vc=3.9514, Pc=0.077796; vl=1.21482, vg=775.35, ps=8.8828e-4,
ps/Pc=0.0114181, omega=0.942408. Matches claim.
