"""Certificate generator (run 2026-11-14T1428Z): one-sided cells (Work/Math/BEOCell.lean, CellProp and
InvProp mirrored exactly; exact rationals only) for the Bonnor-Ebert solution in homology variables
u = s e^w / (-w'), v = -s w' on [150, T]:  s u' = u (3 - u - v),  s v' = v (u - 1).
Start: BEHChain's state at 150 (box radius 2e-7 -> weighted radius 8e-7).
Error norm N(e) = 7 e1^2 + (e1 + 2 e2)^2; one-sided constant mu (per unit log-radius) from the corner test.
Segments (invariant m): [150, A3] m=1 (2u-v>0); [A3, B3] m=4 (G<0); [B3, A4] m=2 (2u-v<0);
[A4, B4] m=3 (G>0); [B4, T] m=1.  G = 6u - 2u^2 - 3uv + v.
usage: gen_bo.py A3 B3 A4 B4 T out.json   (A3.. as decimal strings)
"""
from fractions import Fraction as F
import math, sys, json

N = 12
DEN = 10 ** 30
KH = F(1, 16)

def rnd(x, d=DEN): return F(round(x * d), d)
def ceil_q(x, d): return F(math.ceil(x * d), d)
def floor_q(x, d): return F(math.floor(x * d), d)

def qadd(p, q):
    n = max(len(p), len(q)); return [(p[i] if i < len(p) else 0) + (q[i] if i < len(q) else 0) for i in range(n)]
def qsmul(c, p): return [c * a for a in p]
def qsub(p, q): return qadd(p, qsmul(-1, q))
def qmul(p, q):
    if not p or not q: return []
    r = [F(0)] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        for j, b in enumerate(q): r[i + j] += a * b
    return r
def qderiv(p): return [i * p[i] for i in range(1, len(p))]
def qeval(p, x):
    r = F(0)
    for a in reversed(p): r = r * x + a
    return r
def qabs(p, h): return qeval([abs(a) for a in p], h)
def lo(p, h): return (p[0] if p else 0) - h * qabs(p[1:], h)
def hi(p, h): return (p[0] if p else 0) + h * qabs(p[1:], h)

def taylor(t0, u0, v0):
    a, b = [u0], [v0]
    for k in range(N):
        uu = sum(a[i] * a[k - i] for i in range(k + 1)); uv = sum(a[i] * b[k - i] for i in range(k + 1))
        f1 = 3 * a[k] - uu - uv
        f2 = uv - b[k]
        a.append((f1 - k * a[k]) / (t0 * (k + 1)))
        b.append((f2 - k * b[k]) / (t0 * (k + 1)))
    return [u0] + [rnd(c) for c in a[1:]], [v0] + [rnd(c) for c in b[1:]]

def du1(t0, pu, pv): return qsub(qmul([t0, F(1)], qderiv(pu)), qmul(pu, qsub(qsub([F(3)], pu), pv)))
def dv1(t0, pu, pv): return qsub(qmul([t0, F(1)], qderiv(pv)), qmul(pv, qsub(pu, [F(1)])))
def gp(pu, pv): return qsub(qsmul(2, pu), pv)
def Gp(pu, pv): return qadd(qsub(qsub(qsmul(6, pu), qsmul(2, qmul(pu, pu))), qsmul(3, qmul(pu, pv))), pv)
def NwQ(e1, e2): return 7 * e1 ** 2 + (e1 + 2 * e2) ** 2

def corner_ok(m1, m2, mu):
    a = 16 * m1 + 6 * m2 + 8 * mu - 24; b = 10 * m1 - 2 * m2 + 4 * mu - 4; c = -2 * m1 + 4 * mu + 4
    return a > 0 and b * b <= 4 * a * c

def sqrt_up(x, d=10 ** 40):
    # rational s >= sqrt(x)
    s = ceil_q(F(math.isqrt(int(x * d * d)) + 1, d), d)
    assert s * s >= x
    return s

def best_mu(UL, UH, VL, VH):
    lo_, hi_ = F(-1), F(0)
    if not all(corner_ok(m1, m2, hi_) for m1 in (UL, UH) for m2 in (VL, VH)): return None
    for _ in range(30):
        mid = (lo_ + hi_) / 2
        if all(corner_ok(m1, m2, mid) for m1 in (UL, UH) for m2 in (VL, VH)): hi_ = mid
        else: lo_ = mid
    return ceil_q(hi_, 10 ** 6)

def start():
    return F(2105111091, 2000000000), F(2331774279, 1250000000), 4 * F(1, 5000000)

def grid(marks, T):
    # refine towards a bracket start (geometric, halving the distance) and away from a bracket end
    g = [F(150)]; t = F(150)
    A3, B3, A4, B4 = marks
    for target in marks + [T]:
        while t < target:
            h = F(math.floor(t * KH * 2 ** 12), 2 ** 12)
            d = target - t
            if target in (A3, A4) and d < t / 8:
                h = min(h, max(F(1, 2 ** 12), F(math.floor(d / 2 * 2 ** 12), 2 ** 12)))
            if target in (A4, T) and t - (B3 if target == A4 else B4) < t / 8:
                prev = B3 if target == A4 else B4
                h = min(h, max(F(1, 2 ** 8), F(math.floor((t - prev) * 2 ** 12), 2 ** 12)))
            if t + h >= target or target - (t + h) < h / 4 or d <= F(1, 2 ** 11):
                h = target - t
            t = t + h; g.append(t)
    return g

def run(A3, B3, A4, B4, T):
    u0, v0, delta = start()
    gr = grid([A3, B3, A4, B4], T); cells = []
    for i in range(len(gr) - 1):
        t0, h = gr[i], gr[i + 1] - gr[i]
        pu, pv = taylor(t0, u0, v0)
        d1, dxx = du1(t0, pu, pv), None
        dxx = qadd(d1, qsmul(2, dv1(t0, pu, pv)))
        qa, qb = qabs(d1, h), qabs(dxx, h)
        eps = ceil_q(sqrt_up(7 * qa ** 2 + qb ** 2) / t0 * (1 + F(1, 10 ** 6)), 10 ** 40)
        assert 7 * qa ** 2 + qb ** 2 < (eps * t0) ** 2
        B = ceil_q(delta + eps * h, 10 ** 40)
        UL = floor_q(lo(pu, h) - B - F(1, 10 ** 9), 10 ** 9)
        UH = ceil_q(hi(pu, h) + B + F(1, 10 ** 9), 10 ** 9)
        VL = floor_q(lo(pv, h) - B - F(1, 10 ** 9), 10 ** 9)
        VH = ceil_q(hi(pv, h) + B + F(1, 10 ** 9), 10 ** 9)
        mu = best_mu(UL, UH, VL, VH)
        assert mu is not None, ('corner', float(t0))
        Be = ceil_q(delta * (1 / (1 - mu / (t0 + h) * h)) + eps * h, 10 ** 40)
        ue, ve = qeval(pu, h), qeval(pv, h)
        nu, nv = rnd(ue), rnd(ve)
        nd = ceil_q(Be + sqrt_up(NwQ(ue - nu, ve - nv)) + F(1, 10 ** 40), 10 ** 40)
        t1 = t0 + h
        if t1 <= A3: m = 1
        elif t1 <= B3: m = 4
        elif t1 <= A4: m = 2
        elif t1 <= B4: m = 3
        else: m = 1
        UHVH = (7 + 7 * UH + 3 * VH) * B
        marg = {1: lo(gp(pu, pv), h) - 3 * B, 2: -(hi(gp(pu, pv), h) + 3 * B),
                3: lo(Gp(pu, pv), h) - UHVH, 4: -(hi(Gp(pu, pv), h) + UHVH)}[m]
        cells.append(dict(t0=t0, h=h, delta=delta, eps=eps, B=B, Be=Be, mu=mu, UL=UL, UH=UH, VL=VL, VH=VH,
                          pu=pu, pv=pv, m=m, marg=marg, nu=nu, nv=nv, nd=nd))
        u0, v0, delta = nu, nv, nd
    return cells

if __name__ == '__main__':
    A3, B3, A4, B4, T = (F(x) for x in sys.argv[1:6])
    cells = run(A3, B3, A4, B4, T)
    bad = [c for c in cells if c['marg'] <= 0]
    for c in cells[::10] + cells[-1:]:
        print('%10.3f h=%8.3f m=%d B=%.3e Be=%.3e mu=%.4f eps=%.2e marg=%.2e' % (float(c['t0']), float(c['h']), c['m'],
              float(c['B']), float(c['Be']), float(c['mu']), float(c['eps']), float(c['marg'])), file=sys.stderr)
    print('cells', len(cells), 'fails', len(bad), file=sys.stderr)
    for c in bad[:10]: print('FAIL', c['m'], float(c['t0']), float(c['marg']), file=sys.stderr)
    for m in (4, 3):
        br = [c for c in cells if c['m'] == m]
        for c in br:
            h = c['h']
            print('bracket m=%d [%s, %s] u in [%.10f, %.10f] v in [%.10f, %.10f] B %.2e' % (m, c['t0'], c['t0'] + h,
                  float(lo(c['pu'], h) - c['B']), float(hi(c['pu'], h) + c['B']),
                  float(lo(c['pv'], h) - c['B']), float(hi(c['pv'], h) + c['B']), float(c['B'])), file=sys.stderr)
    e = cells[-1]; print('end u v', float(e['nu']), float(e['nv']), 'delta', float(e['nd']), file=sys.stderr)
    json.dump([{k: (str(v) if isinstance(v, F) else ([str(x) for x in v] if isinstance(v, list) else v)) for k, v in c.items()} for c in cells], open(sys.argv[6], 'w'))
