"""Floating point (run 2026-11-05T1228Z, not certified): Peng-Robinson (u=2, w=-1) with Soave alpha and the
Robinson-Peng 1978 kappa(omega) at omega = 1 (run 2026-11-05T1828Z; copied from run 1228Z's pr_float.py, kappa changed); reduced variables x = v/b, theta = RTb/a(T), pi = p b^2/a(T).
Maxwell equal areas via the closed-form primitive psi; prints theta_c, theta(0.7), pi_s, ps/Pc, omega."""
from mpmath import mp, mpf, sqrt, log, log10, polyroots, findroot
mp.dps = 40
r2 = sqrt(2)
xc = findroot(lambda x: x**3 - 3*x**2 - 3*x - 3, 4)
D = lambda x: x*x + 2*x - 1
# critical: theta_c from P' = 0: theta/(x-1)^2 = (2x+2)/D^2
thc = (2*xc + 2) * (xc - 1)**2 / D(xc)**2
pic = thc/(xc - 1) - 1/D(xc)
def run(omega):
    k = mpf('0.379642') + mpf('1.48503')*omega - mpf('0.164423')*omega**2 + mpf('0.016666')*omega**3
    al = (1 + k*(1 - sqrt(mpf(7)/10)))**2
    th = mpf(7)/10*thc/al
    g = lambda x: th/(x-1) - 1/D(x)
    psi = lambda p, x: th*log(x-1) + (log(x+1+r2) - log(x+1-r2))/(2*r2) - p*x
    def roots(p):  # p (x-1) D = th D - (x-1)
        # p(x^3 + x^2 - 3x + 1) - th(x^2+2x-1) + (x - 1) = 0
        c = [p, p - th, -3*p - 2*th + 1, p + th - 1]
        return sorted([z.real for z in polyroots(c, maxsteps=200, extraprec=60) if abs(z.imag) < mpf(10)**-25 and z.real > 1])
    def F(p):
        r = roots(p); return psi(p, r[-1]) - psi(p, r[0])
    # bracket
    ps = [pic*mpf(i)/2000 for i in range(1, 2000)]
    vals = [(p, F(p)) for p in ps if len(roots(p)) == 3]
    for (p1, f1), (p2, f2) in zip(vals, vals[1:]):
        if f1*f2 < 0:
            lo, hi = p1, p2
            for _ in range(150):
                m = (lo+hi)/2
                if F(m)*f1 > 0: lo = m
                else: hi = m
            pr = lo
            # actual pressure ratio: ps/Pc = (pi_s a(T)/b^2)/(pic ac/b^2) = pi_s*al/pic
            ratio = pr*al/pic
            r = roots(pr)
            return dict(kappa=k, alpha=al, theta=th, pi_s=pr, xl=r[0], xg=r[-1], ratio=ratio, omega=-log10(ratio)-1)
print('xc', xc, 'theta_c', thc, 'pi_c', pic)
for w in ['0', '1']:
    d = run(mpf(w))
    print(w, {k: mp.nstr(v, 15) for k, v in d.items()})
