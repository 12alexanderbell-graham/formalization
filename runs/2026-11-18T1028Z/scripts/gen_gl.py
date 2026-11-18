"""Certificate generator (run 2026-11-18T1028Z): the regular isothermal (Gelfand) solution in homology
variables u = s e^w / (-w'), v = -s w', s u' = u (3 - u - v), s v' = v (u - 1), from A = 4.071496844
(start box from Checked.Math.GCerts.chain: e^{w(A)}, w'(A)) to the second turning point of
lambda = s^2 e^w = u v. Cells mirror Checked/Math/BEHCell.lean (CellProp) exactly; exact rationals.
Segments (invariant m of Work/Math/GLamCell.lean):
  [A, B0]   m 0 (none; B0 = 4.071496845)
  [B0, P1]  m 1 (v > 2)
  [P1, Q1]  m 4 (u < 1: v decreasing; holds the second zero of v - 2)
  [Q1, P2]  m 2 (v < 2)
  [P2, Q2]  m 3 (u > 1: v increasing; holds the third zero of v - 2)
  end at Q2 with v(Q2) > 2 read off the end enclosure.
"""
from fractions import Fraction as F
import math, sys, json

N = 12
DEN = 10 ** 30
A = F(1017874211, 250000000)
B0 = F(814299369, 200000000)
P1 = F(sys.argv[1]); Q1 = F(sys.argv[2]); P2 = F(sys.argv[3]); Q2 = F(sys.argv[4])
KH = F(1, 12)

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

def start():
    EC, R = F(1001983101246205873, 5000000000000000000), F(31316544345759, 10 ** 25)
    PC = F(-3070123956454913517, 6250000000000000000)
    E1, E2, P1_, P2_ = EC - R, EC + R, PC - R, PC + R
    ulo, uhi = A * E1 / (-P1_), A * E2 / (-P2_)
    vlo, vhi = -A * P2_, -A * P1_
    u0, v0 = rnd((ulo + uhi) / 2, 10 ** 20), rnd((vlo + vhi) / 2, 10 ** 20)
    d = ceil_q(max(u0 - ulo, uhi - u0, v0 - vlo, vhi - v0), 10 ** 20)
    return u0, v0, d

def margin(m, pu, pv, h, Bc):
    if m == 1: return lo(pv, h) - Bc - 2
    if m == 2: return 2 - (hi(pv, h) + Bc)
    if m == 3: return lo(pu, h) - Bc - 1
    if m == 4: return 1 - (hi(pu, h) + Bc)
    return F(1)

def mk(t0, h, u0, v0, delta, m):
    pu, pv = taylor(t0, u0, v0)
    UL = floor_q(lo(pu, h) - F(1, 100) - F(1, 10 ** 6), 10 ** 6)
    UH = ceil_q(hi(pu, h) + F(1, 100) + F(1, 10 ** 6), 10 ** 6)
    VL = floor_q(lo(pv, h) - F(1, 100) - F(1, 10 ** 6), 10 ** 6)
    VH = ceil_q(hi(pv, h) + F(1, 100) + F(1, 10 ** 6), 10 ** 6)
    L1 = max(3 - 2 * UL - VL, 2 * UH + VH - 3)
    L2 = max(UH - 1, 1 - UL)
    K = ceil_q(max(L1 + UH, VH + L2) / t0, 10 ** 6)
    if not (K * h < 1): return None
    Eg = 1 / (1 - K * h)
    eps = ceil_q(max(qabs(du1(t0, pu, pv), h), qabs(dv1(t0, pu, pv), h)) / t0, 10 ** 40)
    Bc = ceil_q(delta * Eg + eps / K * (Eg - 1), 10 ** 40)
    if not (Bc < F(1, 100)): return None
    marg = margin(m, pu, pv, h, Bc)
    if marg <= 0: return None
    ue, ve = qeval(pu, h), qeval(pv, h)
    nu, nv = rnd(ue), rnd(ve)
    nd = ceil_q(Bc + max(abs(ue - nu), abs(ve - nv)), 10 ** 40)
    return dict(t0=t0, h=h, delta=delta, eps=eps, B=Bc, UL=UL, UH=UH, VL=VL, VH=VH, L1=L1, L2=L2,
                K=K, pu=pu, pv=pv, m=m, marg=marg, nu=nu, nv=nv, nd=nd)

def run():
    u0, v0, delta = start()
    cells = []; t = A
    for (target, m) in ((B0, 0), (P1, 1), (Q1, 4), (P2, 2), (Q2, 3)):
        while t < target:
            hmax = F(math.floor(t * KH / 3 * 2 ** 30), 2 ** 30)
            h = min(hmax, target - t)
            if h < 0: h = target - t
            # avoid a tiny last piece
            if target - (t + h) < h / 4: h = target - t
            c = None
            while True:
                c = mk(t, h, u0, v0, delta, m)
                if c is not None: break
                h = h / 2
                if h < F(1, 10 ** 14): raise SystemExit("stuck at t=%s m=%d lastB=%.3e" % (float(t), m, float(cells[-1]["B"])))
                h = F(math.floor(h * 2 ** 50), 2 ** 50)
            cells.append(c)
            t = t + h; u0, v0, delta = c['nu'], c['nv'], c['nd']
    return cells

if __name__ == '__main__':
    cells = run()
    for c in cells[::20] + cells[-3:]:
        print(float(c['t0']), float(c['h']), c['m'], 'B %.3e' % float(c['B']), 'marg %.3e' % float(c['marg']), file=sys.stderr)
    print('cells', len(cells), file=sys.stderr)
    for m, nm in ((4, 'lam1'), (3, 'lam2')):
        br = [c for c in cells if c['m'] == m]
        ulo = min(lo(c['pu'], c['h']) - c['B'] for c in br); uhi = max(hi(c['pu'], c['h']) + c['B'] for c in br)
        print(nm, 'in', '%.12f %.12f' % (float(2 * ulo), float(2 * uhi)), 'bracket cells', len(br), file=sys.stderr)
    e = cells[-1]; print('end v', float(e['nv']), 'delta', float(e['nd']), file=sys.stderr)
    json.dump([{k: (str(v) if isinstance(v, F) else ([str(x) for x in v] if isinstance(v, list) else v)) for k, v in c.items()} for c in cells], open(sys.argv[5], 'w'))
