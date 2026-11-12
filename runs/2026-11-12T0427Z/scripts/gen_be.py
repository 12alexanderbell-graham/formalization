"""Certificate generator for the Bonnor–Ebert critical sphere (run 2026-11-12T0427Z).

Same equation and cell scheme as the Gelfand chain (runs/2026-11-06T1228Z/scripts/gen_g.py, imported as
g_base): w'' + (2/s) w' + e^w = 0, w(0) = 0, cells in E = e^w, phi = w'. Start values at S0 = 1/32 are those
of Checked.Math.GCerts.startI (SDEN = 10^20). Cells to T = 7 in three runs:
  inc  [S0, A]: g = E - phi^2/2 > 0 on each cell (m increasing),
  none [A, B]: the bracket of the critical radius,
  dec  [B, 7]: g < 0 on each cell (m decreasing).
Cell invariant check (Lean BInvProp): gpoly = pe - pp^2/2 on [0, h];
  inc: lo(gpoly) - B(1 + PH) > 0 ;  dec: hi(gpoly) + B(1 + PH) < 0.
Exact rational arithmetic only.
"""
from fractions import Fraction as F
import math, sys, json
import g_base as G
G.S0 = F(1, 64)   # start radius (Gelfand used 1/32: start error 6.9e-19 grew to 3.4e-11 at A)

DEN = 10 ** 30
SDEN = 10 ** 30
T = F(7)
A = F(6450751440, 10 ** 9)     # bracket of xi_c = 6.45075144417...
B = F(64507515, 10 ** 7)       # = the statement's upper end
KH = F(1, 16)
HMAX = F(1, 16)


def taylor(t0, e0, f0):
    E, Ph = [e0], [f0]
    for k in range(G.N):
        E.append(sum(E[i] * Ph[k - i] for i in range(k + 1)) / (k + 1))
        ek1 = E[k - 1] if k >= 1 else F(0)
        Ph.append(-((k + 2) * Ph[k] + t0 * E[k] + ek1) / (t0 * (k + 1)))
    return [e0] + [G.rnd(c, DEN) for c in E[1:]], [f0] + [G.rnd(c, DEN) for c in Ph[1:]]


def simple(h):
    return F(math.floor(h * 2 ** 12), 2 ** 12) if h > F(1, 2 ** 12) else F(math.floor(h * 2 ** 30), 2 ** 30)


def make_grid():
    """Cells of length about KH/K; geometric refinement towards A and B (halving the distance)
    and away from B (growing by half the distance), so that the crude cell bound of g keeps its sign next to the bracket."""
    g = [G.S0]
    t = G.S0
    for target in (A, B, T):
        while t < target:
            K = 2 / t + 1 + F(1, 10)
            h = min(simple(KH / K), HMAX)
            d = target - t
            if target != T and F(1, 2 ** 17) < d < F(1, 20):
                h = min(h, simple(d / 2))
            if target == T and t - B < F(1, 20):
                h = min(h, max(F(1, 2 ** 25), simple((t - B) / 2)))
            if t + h >= target or target - (t + h) < h / 4 or d <= F(1, 2 ** 17):
                h = target - t
            t = t + h
            g.append(t)
    return g


def gpoly(pe, pp):
    return G.add(pe, G.sc(F(-1, 2), G.mul(pp, pp)))


def run():
    P, Pd, W, rho, R, Mp, Rr = G.start()
    sb = G.startbox(P, Pd, W, rho, R, Mp)
    e0, f0, delta = sb['e0'], sb['f0'], sb['delta']
    grid = make_grid()
    cells = []
    for i in range(len(grid) - 1):
        t0, h = grid[i], grid[i + 1] - grid[i]
        pe, pp = taylor(t0, e0, f0)
        EH = G.ceil_q(max(abs(G.lowb(pe, h)), abs(G.upb(pe, h))) + G.M + F(1, 10 ** 6), 10 ** 6)
        PH = G.ceil_q(max(abs(G.lowb(pp, h)), abs(G.upb(pp, h))) + G.M + F(1, 10 ** 6), 10 ** 6)
        K = max(F(1), PH + EH, G.ceil_q(2 / t0 + 1, 10 ** 6))
        assert K * h < 1, (i, float(K * h))
        Eg = 1 / (1 - K * h)
        d1 = G.add(G.deriv(pe), G.sc(-1, G.mul(pe, pp)))
        s = [t0, F(1)]
        d2 = G.add(G.mul(s, G.deriv(pp)), G.sc(2, pp), G.mul(s, pe))
        eps = G.ceil_q(max(G.absb(d1, h), G.absb(d2, h) / t0), 10 ** 40)
        Bc = G.ceil_q(delta * Eg + eps / K * (Eg - 1), 10 ** 40)
        assert Bc < G.M
        ee, fe = G.ev(pe, h), G.ev(pp, h)
        ne, nf = G.rnd(ee, SDEN), G.rnd(fe, SDEN)
        nd = G.ceil_q(Bc + max(abs(ee - ne), abs(fe - nf)), 10 ** 40)
        t1 = t0 + h
        kind = 'inc' if t1 <= A else ('none' if t1 <= B else 'dec')
        gp = gpoly(pe, pp)
        if kind == 'inc':
            marg = G.lowb(gp, h) - Bc * (1 + PH)
        elif kind == 'dec':
            marg = -(G.upb(gp, h) + Bc * (1 + PH))
        else:
            marg = F(1)
        cells.append(dict(i=i, t0=t0, h=h, pe=pe, pp=pp, eps=eps, delta=delta, B=Bc, K=K, EH=EH,
                          PH=PH, ne=ne, nf=nf, nd=nd, kind=kind, marg=marg))
        e0, f0, delta = ne, nf, nd
    return sb, cells


if __name__ == '__main__':
    sb, cells = run()
    bad = [c for c in cells if c['marg'] <= 0]
    for c in cells[::20] + cells[-3:]:
        print(c['i'], float(c['t0']), float(c['h']), c['kind'], 'B', float(c['B']), 'marg', float(c['marg']), file=sys.stderr)
    for c in bad:
        print('FAIL', c['i'], c['kind'], float(c['t0']), float(c['h']), float(c['marg']), file=sys.stderr)
    gap = [c for c in cells if c['kind'] == 'none']
    print('cells', len(cells), 'gap cells', len(gap), 'fails', len(bad), file=sys.stderr)
    # values at A (start of gap cell): E, phi with radius delta
    ga = gap[0]
    print('at A: E', float(ga['pe'][0]), 'phi', float(ga['pp'][0]), 'delta', float(ga['delta']), file=sys.stderr)
