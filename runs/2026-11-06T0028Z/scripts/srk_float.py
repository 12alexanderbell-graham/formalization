"""Floating point (run 2026-11-06T0028Z, not certified): SRK (u=1, w=0) with Soave's alpha and
Soave's 1972 kappa(omega) = 0.480 + 1.574 omega - 0.176 omega^2 at omega = 1, Maxwell equal areas in
reduced variables x = v/b, theta = RTb/a(T), pi = p b^2/a(T). Prints theta, pi_s, x_l, x_g, p_s/P_c, omega_out."""
from mpmath import mp, mpf, sqrt, cbrt, log, log10, polyroots, findroot
mp.dps = 40
c = cbrt(mpf(2)); xc = c*c + c + 1                 # root of x^3 - 3x^2 - 3x - 1 (RK critical point)
import sys
s = sqrt(mpf(7)/10); kap = mpf(sys.argv[1]) if len(sys.argv) > 1 else mpf('0.480') + mpf('1.574') - mpf('0.176')
al = (1 + kap*(1 - s))**2
K = 3*xc - 9 - 9/xc                                 # R Tc b / a_c
th = mpf(7)/10*K/al
g = lambda x: th/(x-1) - 1/(x*x+x)
psi = lambda p, x: th*log(x-1) + log(x+1) - log(x) - p*x
def roots(p):
    return sorted([z.real for z in polyroots([p, -th, -p-th+1, -1], maxsteps=400, extraprec=200) if abs(z.imag) < mpf(10)**-20 and z.real > 1])
def F(p):
    r = roots(p); return psi(p, r[-1]) - psi(p, r[0])
lo, hi = mpf('1e-6'), mpf('1e-3')
# bracket by scan
ps = [mpf(i)/10**7 for i in range(1, 20000, 5)]
prev = None
for p in ps:
    r = roots(p)
    if len(r) < 3: continue
    v = F(p)
    if prev is not None and prev[1]*v < 0:
        lo, hi = prev[0], p; break
    prev = (p, v)
pis = findroot(F, (lo, hi), solver='bisect' if False else 'anderson')
r = roots(pis)
Ob = xc**2/3 - xc - 1
ratio = pis*al*(xc/9)/Ob**2
print('alpha', al); print('theta', th); print('pi_s', pis); print('x_l', r[0], 'x_g', r[-1])
print('ps/Pc', ratio); print('omega', -log10(ratio) - 1)
