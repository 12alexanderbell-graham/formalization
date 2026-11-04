"""Floating-point side computation (run 2026-11-04T1828Z, not certified): feed Soave's kappa(omega)
correlations back into SRK (u=1, w=0) and PR (u=2, w=-1) and compute the acentric factor each
equation itself predicts at T_r = 0.7 (Maxwell equal areas in reduced variables). Prints
omega_in, omega_out - omega_in for SRK and PR (PR 1976 kappa)."""
from mpmath import mp, mpf, sqrt, log, log10, polyroots, findroot, diff
mp.dps = 30

def crit(u, w):
    def sysf(T, v):
        P = lambda x: T / (x - 1) - 1 / (x * x + u * x + w)
        return [diff(P, v), diff(P, v, 2)]
    T, v = findroot(sysf, [mpf('0.2'), mpf('3')])
    return T, v, T / (v - 1) - 1 / (v * v + u * v + w)

def omega(u, w, alpha):
    Tc, vc, Pc = crit(u, w)
    T = mpf('0.7') * Tc; a = alpha(mpf('0.7'))
    def roots(p):
        c = [p, p * (u - 1) - T, p * (w - u) - T * u + a, -p * w - T * w - a]
        return sorted([x.real for x in polyroots(c) if abs(x.imag) < 1e-20 and x.real > 1])
    def F(p):
        r = roots(p); vl, vg = r[0], r[-1]
        from mpmath import quad
        return T * log((vg - 1) / (vl - 1)) - quad(lambda s: a / (s * s + u * s + w), [vl, vg]) - p * (vg - vl)
    pts = [Pc * mpf(i) / 400 for i in range(1, 400)]
    vals = [(p, F(p)) for p in pts if len(roots(p)) == 3]
    for (p1, f1), (p2, f2) in zip(vals, vals[1:]):
        if f1 * f2 < 0:
            lo, hi = p1, p2
            for _ in range(100):
                m = (lo + hi) / 2
                if F(m) * f1 > 0: lo = m
                else: hi = m
            return -log10(lo / Pc) - 1
soave = lambda k: (lambda tr: (1 + k * (1 - sqrt(tr))) ** 2)
for w in ['0', '0.1', '0.2', '0.3', '0.4', '0.5', '0.7', '1.0']:
    w = mpf(w)
    ks = mpf('0.480') + mpf('1.574') * w - mpf('0.176') * w ** 2
    kp = mpf('0.37464') + mpf('1.54226') * w - mpf('0.26992') * w ** 2
    print(float(w), float(omega(1, 0, soave(ks)) - w), float(omega(2, -1, soave(kp)) - w))
