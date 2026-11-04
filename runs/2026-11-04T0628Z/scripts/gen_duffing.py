"""Certificate generator for the Duffing enclosure (run 2026-11-04T0628Z).

Exact rational arithmetic only (fractions.Fraction). For each cell [t_i, t_i + h]:
  * P_i = (Px, Pv): Taylor polynomials (degree N) of the solution through the rounded state
    (x_i, v_i), coefficients rounded to denominator DEN;
  * defect polynomials D1 = Px' - Pv, D2 = Pv' + Px + Px^3 (exact), eps_i >= sum |c_k| h^k;
  * box checks |Px| <= X, |Pv| <= V on [0, h] (sum |c_k| h^k);
  * Groenwall: B_i = delta_i * E + eps_i / K * (E - 1), E = 1/(1 - K h) >= exp(K h);
  * next state: rounding of P_i(h); delta_{i+1} >= B_i + rounding error.
Then the sign checks for the headline. Emits Lean (emit_lean) — no hand transcription.
"""
from fractions import Fraction as F
import math, sys, json

N = 7
DEN = 10 ** 11
SDEN = 10 ** 12
h = F(1, 20)
NC = 24          # cells: [0, 6/5]
X, V = F(101, 100), F(13, 10)
K = F(41, 10)    # >= 1 + 3 X^2 = 4.0603
E = 1 / (1 - K * h)   # exp(K h) < 1/(1 - K h)   (Mathlib exp_bound_div_one_sub_of_interval')
LO, HI = F(1192005, 10 ** 6), F(1192006, 10 ** 6)


def rnd(q, d):
    return F(round(q * d), d)


def taylor(x0, v0):
    xs, vs = [x0], [v0]
    for k in range(N):
        # (x^3)_k
        c3 = F(0)
        for i in range(k + 1):
            for j in range(k + 1 - i):
                c3 += xs[i] * xs[j] * xs[k - i - j]
        xs.append(vs[k] / (k + 1))
        vs.append(-(xs[k] + c3) / (k + 1))
    return [x0] + [rnd(c, DEN) for c in xs[1:]], [v0] + [rnd(c, DEN) for c in vs[1:]]


def ev(p, s):
    r = F(0)
    for c in reversed(p):
        r = c + s * r
    return r


def deriv(p):
    return [k * p[k] for k in range(1, len(p))] or [F(0)]


def add(p, q):
    n = max(len(p), len(q))
    return [(p[i] if i < len(p) else 0) + (q[i] if i < len(q) else 0) for i in range(n)]


def mul(p, q):
    r = [F(0)] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        for j, b in enumerate(q):
            r[i + j] += a * b
    return r


def neg(p):
    return [-c for c in p]


def absb(p, s=h):
    return sum(abs(c) * s ** k for k, c in enumerate(p))


def lowb(p, s=h):   # p(u) >= c0 - sum_{k>=1} |c_k| s^k on [0, s]
    return p[0] - sum(abs(c) * s ** k for k, c in enumerate(p) if k >= 1)


def upb(p, s=h):
    return p[0] + sum(abs(c) * s ** k for k, c in enumerate(p) if k >= 1)


def ceil_q(q, d=10 ** 15):
    return F(math.ceil(q * d), d)


cells = []
x0, v0 = F(1), F(0)
delta = F(0)
for i in range(NC):
    px, pv = taylor(x0, v0)
    assert px[0] == x0 and pv[0] == v0
    d1 = add(deriv(px), neg(pv))
    d2 = add(add(deriv(pv), px), mul(px, mul(px, px)))
    eps = ceil_q(max(absb(d1), absb(d2)))
    assert absb(px) <= X and absb(pv) <= V
    B = ceil_q(delta * E + eps / K * (E - 1))
    xe, ve = ev(px, h), ev(pv, h)
    nx, nv = rnd(xe, SDEN), rnd(ve, SDEN)
    ndelta = ceil_q(B + max(abs(xe - nx), abs(ve - nv)))
    cells.append(dict(i=i, t0=i * h, px=px, pv=pv, d1=d1, d2=d2, eps=eps, delta=delta, B=B,
                      nx=nx, nv=nv, ndelta=ndelta))
    x0, v0, delta = nx, nv, ndelta

# sign structure
# positivity by crude lower bound on cells 0..m-1, monotonicity (v < 0) on cells m..23 up to LO
m = 0
while m < NC and lowb(cells[m]['px']) - cells[m]['B'] > 0:
    m += 1
print('crude positivity cells: 0..', m - 1, file=sys.stderr)
last = cells[-1]
assert last['t0'] <= LO < HI <= last['t0'] + h
for c in cells[m:]:
    assert upb(c['pv']) + c['B'] < 0, c['i']
xlo = ev(last['px'], LO - last['t0'])
xhi = ev(last['px'], HI - last['t0'])
print('B last', float(last['B']), 'x(lo) >=', float(xlo - last['B']), 'x(hi) <=',
      float(xhi + last['B']), file=sys.stderr)
assert xlo - last['B'] > 0 and xhi + last['B'] < 0
for c in cells:
    print(c['i'], float(c['eps']), float(c['B']), file=sys.stderr)
json.dump(dict(m=m, cells=[{k: (str(v) if isinstance(v, F) else [str(a) for a in v] if isinstance(v, list) else v)
                            for k, v in c.items()} for c in cells]),
          open(sys.argv[1] if len(sys.argv) > 1 else '/dev/null', 'w'))
