# CDL 2019 (211) vs (223): f0 from the paper's own (39)+(41) at z=0 (kappa=1, rho_m0 = 3H0^2 Om),
# R = -6(Hdot + 2H^2) (38). X = 3 H0 Rdot0 f''(R0) (vanishes in LCDM; dropped in both (211) and (223)).
import sympy as sp
H0, Om, R0, f0, F0, X = sp.symbols('H0 Omega_m0 R0 f0 F0 X')
eq39 = sp.Eq(H0**2, sp.Rational(1, 3)*(3*H0**2*Om/F0 + (1/F0)*((f0 - R0*F0)/2 - X)))
sol = sp.solve(eq39, f0)[0]
print('f0 from (39)+(41):', sp.expand(sol))
print('(223) printed - derived (X=0):', sp.simplify(F0*(6*H0**2 + R0) - 6*H0**2*Om - sol.subs(X, 0)))
print('(211) printed - derived (F0=1, X=0):', sp.simplify(R0 + 6*H0**2*(Om - 1) - sol.subs({X: 0, F0: 1})))
# LCDM: f(R) = R + 2Lambda, Lambda = 3H0^2(1-Om) solves (31)/(39)-(42) exactly (Lean: FRCosmo.lcdm_witness)
