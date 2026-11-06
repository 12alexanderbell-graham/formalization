"""Thomas-Fermi shooting certificates (run 2026-11-06T1828Z).
System in t = sqrt(x), w = sqrt(y), P = y':  w' = t P / w,  P' = 2 w^3.
Per cell [t0, t0+h]: qw, qp = rational Taylor polynomials (degree n) of the exact solution
through the start z, plus a margin (super: +mu*sigma, sub: -mu*sigma) so that
 d1 = qw qw' - (t0+sigma) qp  and  d2 = qp' - 2 qw^3
are > 0 (super) / < 0 (sub) on [0,h] by the crude bound of LECell.lower_of / upper_of
(c0 -/+ h * sum |c_{k+1}| h^k), checked exactly with Fractions.
Next start: qw(h), qp(h) rounded up (super) / down (sub) to DIG decimals."""
import mpmath as mp
from fractions import Fraction as F
import json, sys
mp.mp.dps = 60
DIG = 30  # decimals of rounding

def taylor(t0, zw, zp, n):
    a = [mp.mpf(zw)]; b = [mp.mpf(zp)]
    t0 = mp.mpf(t0)
    for k in range(n):
        # b_{k+1}: (k+1) b_{k+1} = 2 [w^3]_k
        w2 = [sum(a[i]*a[j-i] for i in range(j+1)) for j in range(k+1)]
        w3k = sum(w2[j]*a[k-j] for j in range(k+1))
        b.append(2*w3k/(k+1))
        # a_{k+1}: sum_{i=0}^{k} a_i (k-i+1) a_{k-i+1} = t0 b_k + b_{k-1}
        rhs = t0*b[k] + (b[k-1] if k >= 1 else 0)
        s = sum(a[i]*(k-i+1)*a[k-i+1] for i in range(1, k+1))
        a.append((rhs - s)/((k+1)*a[0]))
    return a, b

def rat(x, dig=DIG):
    return F(int(mp.nint(x*mp.mpf(10)**dig)), 10**dig)

def rup(x: F, dig=DIG):
    d = 10**dig; n = -((-x.numerator*d)//x.denominator); return F(n, d)
def rdown(x: F, dig=DIG):
    d = 10**dig; n = (x.numerator*d)//x.denominator; return F(n, d)

def pmul(p, q):
    r = [F(0)]*(len(p)+len(q)-1)
    for i, x in enumerate(p):
        if x == 0: continue
        for j, y in enumerate(q):
            r[i+j] += x*y
    return r
def padd(p, q):
    n = max(len(p), len(q)); return [(p[i] if i < len(p) else 0) + (q[i] if i < len(q) else 0) for i in range(n)]
def pscale(c, p): return [c*x for x in p]
def pder(p): return [k*p[k] for k in range(1, len(p))] or [F(0)]
def peval(p, s):
    r = F(0)
    for c in reversed(p): r = r*s + c
    return r
def crude_lo(p, h):  # c0 - h * sum |c_{k+1}| h^k
    return p[0] - h*sum(abs(c)*h**k for k, c in enumerate(p[1:]))
def crude_hi(p, h):
    return p[0] + h*sum(abs(c)*h**k for k, c in enumerate(p[1:]))

def defects(qw, qp, t0):
    d1 = padd(pmul(qw, pder(qw)), pscale(-1, pmul([F(t0), F(1)], qp)))
    d2 = padd(pder(qp), pscale(-2, pmul(pmul(qw, qw), qw)))
    return d1, d2

def cell(t0, zw, zp, h, n, sign, muw, cfac):
    a, b = taylor(mp.mpf(t0.numerator)/t0.denominator, mp.mpf(zw.numerator)/zw.denominator,
                  mp.mpf(zp.numerator)/zp.denominator, n)
    qw = [zw] + [rat(x) for x in a[1:]]
    qp = [zp] + [rat(x) for x in b[1:]]
    zwf = float(zw)
    mup = rat(mp.mpf(cfac*12*max(zwf, 0.0)**2*float(h))*mp.mpf(muw.numerator)/muw.denominator, 40) + F(1, 10**45)
    qw[1] += sign*muw
    qp[1] += sign*mup
    d1, d2 = defects(qw, qp, t0)
    if sign > 0:
        ok1 = crude_lo(d1, h) > 0; ok2 = crude_lo(d2, h) > 0
    else:
        ok1 = crude_hi(d1, h) < 0; ok2 = crude_hi(d2, h) < 0
    ew, ep = peval(qw, h), peval(qp, h)
    return dict(qw=qw, qp=qp, d1=d1, d2=d2, ok=(ok1 and ok2), ok1=ok1, ok2=ok2, ew=ew, ep=ep, mup=mup)

def chain(sign, s0, h, n, muw, cfac, tmax, stop):
    t0 = F(0)
    zw = F(1) + sign*F(1, 10**25)
    zp = s0
    cells = []
    while True:
        c = cell(t0, zw, zp, h, n, sign, muw, cfac)
        if not c['ok']:
            print('FAIL at', float(t0), c['ok1'], c['ok2'], float(crude_lo(c['d1'], h)), float(crude_lo(c['d2'], h)), file=sys.stderr)
            return cells, False
        c['t0'] = t0
        cells.append(c)
        t0 = t0 + h
        zw = rup(c['ew']) if sign > 0 else rdown(c['ew'])
        zp = rup(c['ep']) if sign > 0 else rdown(c['ep'])
        c['nw'], c['np'] = zw, zp
        if stop(t0, c) or t0 >= tmax:
            return cells, True

if __name__ == '__main__':
    h = F(1, int(sys.argv[1])); n = int(sys.argv[2]); muw = F(1, 10**int(sys.argv[3]))
    lo = F(-158807103, 100000000); hi = F(-158807102, 100000000)
    def stop_sup(t, c):
        return float(c['ew']) < 0.06
    def stop_sub(t, c):
        return c['ep'] > 0
    for name, sign, s0, stop in [('sup', 1, lo, stop_sup), ('sub', -1, hi, stop_sub)]:
        cells, ok = chain(sign, s0, h, n, muw, 1.0, F(12), stop)
        last = cells[-1]
        print(name, ok, len(cells), float(cells[-1]['t0'] + h), float(last['ew']), float(last['ep']))
