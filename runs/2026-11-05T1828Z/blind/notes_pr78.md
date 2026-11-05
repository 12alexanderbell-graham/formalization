# Notes (blind restatement, PR78 acentric)
- kappa, aT, P defined directly; kappa passed as a parameter (instantiated at `kappa 1`); aT uses T_c in sqrt(T/T_c).
- Hypotheses: R>0, a_c>0, b>0 (sign of R needed physically; claim says "any" gas constant, taken as positive), T_c>0, v_c>b inside IsCritical.
- Critical point: deriv and deriv-of-deriv of v ↦ P v T_c vanish at v_c (function is smooth near v_c>b, so no junk-deriv issue).
- P_c := P(v_c, T_c). Maxwell: b<v_l<v_g (v_l<v_g added, else the integral condition is trivial), P(v_l)=P(v_g)=p_s, interval integral = p_s(v_g−v_l). T = 0.7*T_c.
- Roundings: RoundsTo (p_s/P_c) 0.0100 4; RoundsTo (−logb 10 (p_s/P_c) − 1) 1.000 3. p_s/P_c>0 is not assumed (log junk avoided only because claim itself bounds it: ratio within 5e-5 of 0.01).
- Numeric check (mpmath, R=b=1, T_c=1, ω=1, κ=1.7377...): v_c=3.95137, a_c=5.87736, P_c=0.0777961 (Z_c=0.3074).
  Maxwell at T=0.7: v_l=1.20921, v_g=887.053 (middle root 10.71 unused), p_s=7.77802e-4.
  p_s/P_c=0.00999795 -> 0.0100 at 4 decimals OK (|diff|=2.0e-6 ≤ 5e-5); ω_out=1.000089 -> 1.000 at 3 decimals OK (|diff|=8.9e-5 ≤ 5e-4).
- Claim matches numerics. Scratch: /tmp/claude-0/blind78/. Statement compiles with sorry only.
