"""Run 2026-11-25T1828Z: hypothesis 1 of the curved pair with the sine kept. For k in [-1/10, 0] and m just above the
edge where y first vanishes on [w5, 1], the exact residual difference 5 log10(2 S(J5)/S(J3) * Q3/Q5),
S(J) = sin(sqrt(-k) J)/sqrt(-k), against the 1/4 (l19_sq_curved) and 3/20 (l19_sqg_curved) of the conclusions."""
from mpmath import mp, quad, sqrt, mpf, sin, log10, log, findroot
mp.dps = 30
w3 = sqrt(1/(2*sqrt(2))); w5 = sqrt(1/(4*sqrt(2)))
def y(m, k, v): return m*(1 - v**6) + k*(v**2 - v**6) + v**6
def miny(m, k):
    # y increasing above vmin; vmin^4 = -k/(3(1-m-k))
    c = 1 - m - k
    vmin = (-k/(3*c))**mpf(0.25) if k < 0 else mpf(0)
    v = max(vmin, w5)
    return y(m, k, v)
def J(m, k, a):
    c = 1-m-k
    vmin = (-k/(3*c))**mpf(0.25) if k < 0 else mpf(0)
    pts = [a, a + (1-a)*mpf('1e-6'), a+(1-a)*mpf('1e-3'), a+(1-a)*mpf('0.05'), 1]
    return quad(lambda v: 2/sqrt(y(m, k, v)), pts)
def S(k, x): 
    if k == 0: return x
    r = sqrt(-k); return sin(r*x)/r
x3 = log10(2*sqrt(2)); x5 = log10(4*sqrt(2))
def Q(a2, a3, a4, x): return x + a2*x**2 + a3*x**3 + a4*x**4
fits = {'sq': (mpf('3.075'), mpf('4.466'), mpf('-3.716'), mpf(1)/4), 'sqg': (mpf('3.205'), mpf('3.564'), mpf('-2.510'), mpf(3)/20)}
def edge(k):
    lo, hi = mpf(-0.2), mpf(0.1)
    for _ in range(100):
        mid = (lo+hi)/2
        if miny(mid, k) > 0: hi = mid
        else: lo = mid
    return hi
for k in [mpf(0), mpf(-0.025), mpf(-0.05), mpf(-0.075), mpf(-0.09), mpf(-0.1)]:
    me = edge(k)
    print('k=%.3f edge m=%.8f' % (k, me))
    for d in ['1e-2', '1e-3', '1e-4', '1e-6', '1e-9', '1e-12']:
        m = me + mpf(d)
        J3 = J(m, k, w3); J5 = J(m, k, w5)
        r = 2*S(k, J5)/S(k, J3)
        out = []
        for nm, (a2, a3, a4, b) in fits.items():
            if r <= 0:
                out.append('%s D5<=0 (sine past a half turn)' % nm); continue
            dv = 5*log10(r*Q(a2, a3, a4, x3)/Q(a2, a3, a4, x5))
            out.append('%s %.4f(>%.3f)' % (nm, float(dv), float(b)))
        print('  m=edge+%s J3=%.4f J5=%.4f sqrt(-k)J5=%.3f ratio=%.4f  %s' % (d, float(J3), float(J5), float(sqrt(-k)*J5), float(r), '  '.join(out)))
