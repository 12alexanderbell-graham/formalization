"""Certificate generator (run 2026-11-14T0428Z): the Bonnor–Ebert solution in homology variables
u = s e^w / (-w'), v = -s w' on [7, T], T = 150:  s u' = u (3 - u - v),  s v' = v (u - 1).
Start: the enclosure of (e^{w(7)}, w'(7)) proved by Checked.Math.BEEnd.chain_end.
Cells mirror Work/Math/BEHCell.lean (CellProp) exactly; exact rationals only.
Segments: dec [7, A] (g = 2u - v < 0), bracket [A, B] (one cell, G = 6u - 2u^2 - 3uv + v > 0),
inc [B, T] (g > 0).
"""
from fractions import Fraction as F
import math, sys, json

N = 12
DEN = 10 ** 30
T = F(150)
A = F(int(sys.argv[1]) if len(sys.argv) > 1 else 670075200, 10 ** 7)
B = F(int(sys.argv[2]) if len(sys.argv) > 2 else 670075800, 10 ** 7)
KH = F(1, 12)

def rnd(x, d=DEN):
    return F(round(x * d), d)

def ceil_q(x, d):
    return F(math.ceil(x * d), d)

def floor_q(x, d):
    return F(math.floor(x * d), d)

# polynomial ops mirroring Checked.Sim.QPoly (lists, lowest degree first)
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
        # [u(3-u-v)]_k and [v(u-1)]_k
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

def start():
    E1, E2 = F(5827458572, 10 ** 11), F(5827458573, 10 ** 11)
    P1, P2 = F(-35310595060, 10 ** 11), F(-35310595059, 10 ** 11)
    ulo, uhi = 7 * E1 / (-P1), 7 * E2 / (-P2)
    vlo, vhi = -7 * P2, -7 * P1
    u0, v0 = rnd((ulo + uhi) / 2, 10 ** 15), rnd((vlo + vhi) / 2, 10 ** 15)
    d = ceil_q(max(u0 - ulo, uhi - u0, v0 - vlo, vhi - v0), 10 ** 15)
    return u0, v0, d

def grid():
    g = [F(7)]; t = F(7)
    for target in (A, B, T):
        while t < target:
            h = F(math.floor(t * KH / 3 * 2 ** 12), 2 ** 12)
            d = target - t
            if target == A and d < 4:  # refine towards A
                h = min(h, max(F(1, 2 ** 20), F(math.floor(d / 2 * 2 ** 20), 2 ** 20)))
            if target == T and t - B < 4:
                h = min(h, max(F(1, 2 ** 20), F(math.floor((t - B) * 2 ** 20), 2 ** 20)))
            if t + h >= target or target - (t + h) < h / 4 or d <= F(1, 2 ** 19):
                h = target - t
            t = t + h; g.append(t)
    return g

def run():
    u0, v0, delta = start()
    gr = grid(); cells = []
    for i in range(len(gr) - 1):
        t0, h = gr[i], gr[i + 1] - gr[i]
        pu, pv = taylor(t0, u0, v0)
        UL = floor_q(lo(pu, h) - F(1, 100) - F(1, 10 ** 6), 10 ** 6)
        UH = ceil_q(hi(pu, h) + F(1, 100) + F(1, 10 ** 6), 10 ** 6)
        VL = floor_q(lo(pv, h) - F(1, 100) - F(1, 10 ** 6), 10 ** 6)
        VH = ceil_q(hi(pv, h) + F(1, 100) + F(1, 10 ** 6), 10 ** 6)
        L1 = max(3 - 2 * UL - VL, 2 * UH + VH - 3)
        L2 = max(UH - 1, 1 - UL)
        K = ceil_q(max(L1 + UH, VH + L2) / t0, 10 ** 6)
        assert K * h < 1
        Eg = 1 / (1 - K * h)
        eps = ceil_q(max(qabs(du1(t0, pu, pv), h), qabs(dv1(t0, pu, pv), h)) / t0, 10 ** 40)
        Bc = ceil_q(delta * Eg + eps / K * (Eg - 1), 10 ** 40)
        assert Bc < F(1, 100)
        ue, ve = qeval(pu, h), qeval(pv, h)
        nu, nv = rnd(ue), rnd(ve)
        nd = ceil_q(Bc + max(abs(ue - nu), abs(ve - nv)), 10 ** 40)
        t1 = t0 + h
        kind = 'dec' if t1 <= A else ('br' if t1 <= B else 'inc')
        if kind == 'dec': marg = -(hi(gp(pu, pv), h) + 3 * Bc)
        elif kind == 'inc': marg = lo(gp(pu, pv), h) - 3 * Bc
        else: marg = lo(Gp(pu, pv), h) - (7 + 7 * UH + 3 * VH) * Bc
        cells.append(dict(t0=t0, h=h, delta=delta, eps=eps, B=Bc, UL=UL, UH=UH, VL=VL, VH=VH, L1=L1, L2=L2,
                          K=K, pu=pu, pv=pv, kind=kind, marg=marg, nu=nu, nv=nv, nd=nd))
        u0, v0, delta = nu, nv, nd
    return cells

if __name__ == '__main__':
    cells = run()
    bad = [c for c in cells if c['marg'] <= 0]
    for c in cells[::25] + cells[-2:]:
        print(float(c['t0']), float(c['h']), c['kind'], 'B %.3e' % float(c['B']), 'marg %.3e' % float(c['marg']), file=sys.stderr)
    br = [c for c in cells if c['kind'] == 'br']
    print('cells', len(cells), 'bracket', len(br), 'fails', len(bad), file=sys.stderr)
    for c in bad[:10]: print('FAIL', c['kind'], float(c['t0']), float(c['marg']), file=sys.stderr)
    c = br[0]; h = c['h']
    ulo, uhi = lo(c['pu'], h) - c['B'], hi(c['pu'], h) + c['B']
    print('bracket u in', float(ulo), float(uhi), 'B', float(c['B']), file=sys.stderr)
    pil, pih = F(314159265358979323846, 10 ** 20), F(314159265358979323847, 10 ** 20)
    m2lo = 2 * ulo ** 4 / pih; m2hi = 2 * uhi ** 4 / pil
    print('m in', math.sqrt(m2lo), math.sqrt(m2hi), file=sys.stderr)
    print('contrast in', float(A * A / (2 * uhi ** 2)), float(B * B / (2 * ulo ** 2)), file=sys.stderr)
    e = cells[-1]; print('end u v', float(e['nu']), float(e['nv']), 'delta', float(e['nd']), file=sys.stderr)
    json.dump([{k: (str(v) if isinstance(v, F) else ([str(x) for x in v] if isinstance(v, list) else v)) for k, v in c.items()} for c in cells], open(sys.argv[3] if len(sys.argv) > 3 else '/tmp/claude-0/be/cells.json', 'w'))
