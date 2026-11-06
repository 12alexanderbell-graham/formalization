"""Referee: reconstruct Soave's 1972 procedure (as described by Pina-Martinez et al., FPE 485 (2019) 264):
for omega = 0, 0.05, ..., 0.5 find the exact kappa*(omega) with SRK p_s(0.7 Tc)/Pc = 10^(-1-omega), then a
least-squares quadratic. Compares with the printed 0.480 + 1.574 w - 0.176 w^2 and evaluates both at w = 1."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from mpmath import mp, mpf, findroot, matrix, lu_solve
from srk_routeA_fugacity import solve, kappa
mp.dps = 30
ws = [mpf(k)/20 for k in range(11)]
ks = []
for w in ws:
    k0 = kappa(w)
    ks.append(findroot(lambda k: solve(k, mpf(10)**(-w - 1))[2] - w, (k0, k0 + mpf('0.001')), solver='anderson'))
for w, k in zip(ws, ks):
    print("  omega", mp.nstr(w, 3), " kappa*", mp.nstr(k, 8), " printed", mp.nstr(kappa(w), 8), " diff", mp.nstr(kappa(w) - k, 3))
A = matrix([[1, w, w**2] for w in ws]); y = matrix(ks)
c = lu_solve(A.T*A, A.T*y)
print("least-squares quadratic over [0, 0.5]:", [mp.nstr(t, 6) for t in c])
k1fit = c[0] + c[1] + c[2]
print("refit kappa(1)", mp.nstr(k1fit, 8), " -> omega_out", mp.nstr(solve(k1fit, mpf('0.0102'))[2], 7))
print("kappa*(1) exact", mp.nstr(findroot(lambda k: solve(k, mpf('0.01'))[2] - 1, (mpf('1.888'), mpf('1.889')), solver='anderson'), 10))
