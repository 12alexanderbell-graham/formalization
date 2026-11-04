"""Certificate generator for the Michaelis–Menten enclosure (run 2026-11-04T0828Z).

Reduced system (conservation e = 1 - c, p = 1 - s - c, proved in Lean):
  s' = F1(s, c) = -s + c*s + c,   c' = F2(s, c) = s - c*s - 2*c,   s(0) = 1, c(0) = 0.
Exact rational arithmetic only. For each cell [t_i, t_i + h_i]:
  * Taylor polynomials (degree N) through the rounded state, coefficients rounded to 1/DEN;
  * exact defect polynomials D1 = Ps' - F1(Ps, Pc), D2 = Pc' - F2(Ps, Pc); eps_i >= sum |c_k| h^k;
  * tube: Ps in [SLO + M, SHI - M], Pc in [CLO + M, CHI - M] on [0, h] (crude bounds), so the
    M-tube around the approximation lies in the Lipschitz box;
  * Groenwall: B_i = delta_i E_i + eps_i / K (E_i - 1), E_i = 1/(1 - K h_i), and B_i < M;
  * next state: rounding of P_i(h); delta_{i+1} >= B_i + rounding error.
Headline checks: lowb(Ps + Pc) - 2 B > 1/2 on every cell up to LO (cells end exactly at LO),
and Ps(h) + Pc(h) + 2B < 1/2 at HI (last cell ends exactly at HI).
"""
from fractions import Fraction as F
import math, sys, json

N = 10
DEN = 10 ** 15
SDEN = 10 ** 16
K = F(21, 5)
SLO, SHI, CLO, CHI = F(-1, 10), F(11, 10), F(-1, 10), F(1, 4)
M = F(1, 100)
LO, HI = F(25665, 10000), F(25666, 10000)

# grid: 51 cells of 1/20 up to 51/20 = 2.55, 4 cells of 33/8000 up to LO, one cell to HI
grid = [F(k, 20) for k in range(52)]
for j in range(1, 5):
    grid.append(F(51, 20) + j * F(33, 8000))
assert grid[-1] == LO
grid.append(HI)
grid.append(F(13, 5))   # to the end of the frozen interval (box membership for existence)


def rnd(q, d):
    return F(round(q * d), d)


def taylor(s0, c0):
    ss, cs = [s0], [c0]
    for k in range(N):
        cs_k = sum(cs[i] * ss[k - i] for i in range(k + 1))  # (c*s)_k
        ss.append((-ss[k] + cs_k + cs[k]) / (k + 1))
        cs.append((ss[k] - cs_k - 2 * cs[k]) / (k + 1))
    return [s0] + [rnd(c, DEN) for c in ss[1:]], [c0] + [rnd(c, DEN) for c in cs[1:]]


def ev(p, s):
    r = F(0)
    for c in reversed(p):
        r = c + s * r
    return r


def deriv(p):
    return [k * p[k] for k in range(1, len(p))] or [F(0)]


def add(*ps):
    n = max(len(p) for p in ps)
    return [sum((p[i] if i < len(p) else 0) for p in ps) for i in range(n)]


def mul(p, q):
    r = [F(0)] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        for j, b in enumerate(q):
            r[i + j] += a * b
    return r


def sc(a, p):
    return [a * c for c in p]


def absb(p, s):
    return sum(abs(c) * s ** k for k, c in enumerate(p))


def lowb(p, s):
    return p[0] - sum(abs(c) * s ** k for k, c in enumerate(p) if k >= 1)


def upb(p, s):
    return p[0] + sum(abs(c) * s ** k for k, c in enumerate(p) if k >= 1)


def ceil_q(q, d=10 ** 18):
    return F(math.ceil(q * d), d)


cells = []
s0, c0 = F(1), F(0)
delta = F(0)
for i in range(len(grid) - 1):
    t0, h = grid[i], grid[i + 1] - grid[i]
    E = 1 / (1 - K * h)
    ps, pc = taylor(s0, c0)
    cps = mul(pc, ps)
    d1 = add(deriv(ps), ps, sc(-1, cps), sc(-1, pc))
    d2 = add(deriv(pc), sc(-1, ps), cps, sc(2, pc))
    eps = ceil_q(max(absb(d1, h), absb(d2, h)))
    assert lowb(ps, h) >= SLO + M and upb(ps, h) <= SHI - M, i
    assert lowb(pc, h) >= CLO + M and upb(pc, h) <= CHI - M, i
    B = ceil_q(delta * E + eps / K * (E - 1))
    assert B < M
    se, ce = ev(ps, h), ev(pc, h)
    ns, nc = rnd(se, SDEN), rnd(ce, SDEN)
    ndelta = ceil_q(B + max(abs(se - ns), abs(ce - nc)))
    cells.append(dict(i=i, t0=t0, h=h, ps=ps, pc=pc, d1=d1, d2=d2, eps=eps, delta=delta, B=B,
                      ns=ns, nc=nc, ndelta=ndelta))
    s0, c0, delta = ns, nc, ndelta

for c in cells:
    if c['t0'] + c['h'] > LO:
        continue
    m = lowb(add(c['ps'], c['pc']), c['h']) - 2 * c['B'] - F(1, 2)
    assert m > 0, (c['i'], float(m))
last = [c for c in cells if c['t0'] + c['h'] == HI][0]
val = ev(add(last['ps'], last['pc']), last['h']) + 2 * last['B']
print('margin at HI', float(F(1, 2) - val), file=sys.stderr)
assert val < F(1, 2)
for c in cells:
    print(c['i'], float(c['t0']), float(c['eps']), float(c['B']),
          float(lowb(add(c['ps'], c['pc']), c['h']) - 2 * c['B'] - F(1, 2)), file=sys.stderr)
json.dump(dict(cells=[{k: (str(v) if isinstance(v, F) else [str(a) for a in v] if isinstance(v, list) else v)
                       for k, v in c.items()} for c in cells]),
          open(sys.argv[1] if len(sys.argv) > 1 else '/dev/null', 'w'))
