"""Exact-rational emulation of the H2+ shooting certificate (run 2026-11-26T1628Z, parts 2/5).

Every number is a closed interval of Python Fractions, rounded outward to the grid 2^-P after each operation,
so each inequality printed as a margin is what a Lean certificate over Q (norm_num / decide on rationals) would
have to check. Conventions and series: docstring of h2p_float.py (printed sign of A, Madsen-Peek).

Certificate shape (the plan the Lean side will follow; see the run README section Route):
  (eta)  for k in {k1, k2}: A-bracket [Al, Au] with g(k, Al) < 0 < g(k, Au), g = dM/ds at s = 1 (eta = 0),
         M the solution regular at eta = 1 (s = 0) with M(1) = 1; and M > 0 on s in [0, 1] for every
         (k, A) in the box [k1, k2] x [Al(k1), Au(k2)] (uniqueness of the even root by the Wronskian identity).
  (xi)   under(k1): for every A in [Al(k1), Au(k1)], the solution regular at xi = 1 with L(1) = 1 has L(X) < 0.
         over(k2):  for every A in [Al(k2), Au(k2)], L > 0 on [1, X], L'(X) > 0, and the coefficient
         N(xi) = 2R xi - k xi^2 + A < 0 for xi >= X (so L increases for ever).
Tails: geometric bounds |c_n| <= C r^n proved by induction from the recurrence for n past the last computed
index (the induction step's inequality is printed with its margin).
"""
from fractions import Fraction as F
import sys

P = 300
GRID = F(1, 2 ** P)


def rdown(x):
    return F((x.numerator * 2 ** P) // x.denominator, 2 ** P)


def rup(x):
    return -rdown(-x)


class I:
    __slots__ = ('lo', 'hi')

    def __init__(self, lo, hi=None):
        if hi is None:
            hi = lo
        lo, hi = F(lo), F(hi)
        assert lo <= hi, (lo, hi)
        self.lo, self.hi = rdown(lo), rup(hi)

    def __add__(s, o):
        o = o if isinstance(o, I) else I(o)
        return I(s.lo + o.lo, s.hi + o.hi)
    __radd__ = __add__

    def __neg__(s):
        return I(-s.hi, -s.lo)

    def __sub__(s, o):
        o = o if isinstance(o, I) else I(o)
        return s + (-o)

    def __rsub__(s, o):
        return (-s) + o

    def __mul__(s, o):
        o = o if isinstance(o, I) else I(o)
        ps = [s.lo * o.lo, s.lo * o.hi, s.hi * o.lo, s.hi * o.hi]
        return I(min(ps), max(ps))
    __rmul__ = __mul__

    def __truediv__(s, o):
        o = o if isinstance(o, I) else I(o)
        assert o.lo > 0 or o.hi < 0, 'division by an interval containing 0'
        return s * I(min(1 / o.lo, 1 / o.hi), max(1 / o.lo, 1 / o.hi))

    def mag(s):
        return max(abs(s.lo), abs(s.hi))

    def hull(s, o):
        return I(min(s.lo, o.lo), max(s.hi, o.hi))

    def width(s):
        return s.hi - s.lo

    def __repr__(s):
        return f'[{float(s.lo):.17g}, {float(s.hi):.17g}]'


R = I(2)


def geo_sum(q, m):
    """sum_{n >= m} q^n, 0 <= q < 1 (Fraction)."""
    return q ** m / (1 - q)


def geo_dsum(q, m):
    """sum_{n >= m} n q^(n-1)."""
    return q ** (m - 1) * (m - (m - 1) * q) / (1 - q) ** 2


# ---------------------------------------------------------------- Frobenius series at a regular singular point
def frob_coeffs(alpha0, beta, gamma, Nterms):
    """c_0 = 1, c_{n+1} = (alpha0 + n(n+1)) c_n + beta c_{n-1} + gamma c_{n-2}, all over 2(n+1)^2, times sign.
    alpha0, beta, gamma intervals (sign folded in by the caller)."""
    c = [I(1)]
    for n in range(Nterms):
        t = (alpha0 + n * (n + 1)) * c[n]
        if n >= 1:
            t = t + beta * c[n - 1]
        if n >= 2:
            t = t + gamma * c[n - 2]
        c.append(t / (2 * (n + 1) ** 2))
    return c


def frob_tail(c, alpha0, beta, gamma, r, sgn=1):
    """Geometric bound |c_n| <= C r^n for n > Nterms. Induction step for n >= M = Nterms:
    [(M(M+1)+|alpha0|)... ] checked as F(n) <= 1 uniformly: (n(n+1)+|a0|)/(2(n+1)^2) <= 1/2 + |a0|/(2(M+1)^2)."""
    M = len(c) - 1
    a0, b, g = alpha0.mag(), beta.mag(), gamma.mag()
    Fn = (F(1, 2) + a0 / (2 * (M + 1) ** 2)) / r + b / (2 * (M + 1) ** 2) / r ** 2 + g / (2 * (M + 1) ** 2) / r ** 3
    C = max(c[j].mag() / r ** j for j in (M - 2, M - 1, M))
    return Fn, C, M


def eval_series(c, tail, x):
    """value and derivative of sum c_n x^n at an interval x >= 0, with the tail bound."""
    Fn, C, M = tail
    assert Fn <= 1, f'tail induction fails: {float(Fn)}'
    xm = x.hi
    q = tail_r * xm
    v = I(0)
    d = I(0)
    p = I(1)
    for n, cn in enumerate(c):
        if n >= 1:
            d = d + n * cn * pprev
        v = v + cn * p
        pprev = p
        p = p * x
    assert q < 1
    tv = C * geo_sum(q, M + 1)
    td = C * tail_r * geo_dsum(q, M + 1)
    return v + I(-tv, tv), d + I(-td, td)


tail_r = None


def eta_series(k, A, Nterms=90, r=F(6, 10)):
    """M = sum b_n s^n, b_{n+1} = [(n(n+1) - k + A) b_n + 2k b_{n-1} - k b_{n-2}] / (2(n+1)^2)."""
    a0, b, g = A - k, 2 * k, -k
    c = frob_coeffs(a0, b, g, Nterms)
    return c, frob_tail(c, a0, b, g, r)


def xi_series(k, A, Nterms=90, r=F(6, 10)):
    """L = sum c_n u^n, c_{n+1} = -[(n(n+1) + 2R - k + A) c_n + (2R - 2k) c_{n-1} - k c_{n-2}] / (2(n+1)^2).
    Folded as c_n = (-1)^n e_n: e_{n+1} = [(n(n+1)+a0) e_n - beta e_{n-1} + gamma e_{n-2}]/(2(n+1)^2)."""
    a0 = 2 * R - k + A
    beta = 2 * R - 2 * k
    gamma = -k
    e = frob_coeffs(a0, -beta, gamma, Nterms)
    c = [en if n % 2 == 0 else -en for n, en in enumerate(e)]
    return c, frob_tail(e, a0, -beta, gamma, r)


# ---------------------------------------------------------------- Taylor step at a regular point x0 > 1
def step_basis(k, A, x0, h, Nterms):
    """Fundamental matrix of the xi equation from x0 to x0 + h (columns: data (1,0) and (0,1)), with a geometric
    tail bound. Returns [[L_a, L_b], [dL_a, dL_b]] intervals and the tail data."""
    N0 = 2 * R * x0 - k * x0 * x0 + A
    N1 = 2 * R - 2 * k * x0
    N2 = -k
    D = x0 * x0 - 1
    cols = []
    for init in ((I(1), I(0)), (I(0), I(1))):
        d = list(init)
        for n in range(Nterms):
            t = 2 * x0 * (n + 1) ** 2 * d[n + 1] + (n * (n + 1) + N0) * d[n]
            if n >= 1:
                t = t + N1 * d[n - 1]
            if n >= 2:
                t = t + N2 * d[n - 2]
            d.append(-t / (D * ((n + 1) * (n + 2))))
        cols.append(d)
    # tail: |d_j| <= C r^j for j >= M, induction step F <= 1 (uniform in n >= M - 2 = Nterms - 1)
    x0m = x0.hi if isinstance(x0, I) else F(x0)
    Dl = D.lo
    m = Nterms  # last index computed is Nterms + 1; induction for d_{n+2}, n >= Nterms
    den = Dl * (m + 1) * (m + 2)
    # the r: smallest grid value with F <= 1
    def Fr(r):
        return (2 * x0m / r + (1 + N0.mag() / ((m + 1) * (m + 2))) / r ** 2) / Dl + \
               (N1.mag() / r ** 3 + N2.mag() / r ** 4) / den
    rr = (x0m + (2 * x0m * x0m - 1) ** 0.5) / (x0m * x0m - 1)
    r = F(rr).limit_denominator(1000) * F(1001, 1000)
    while Fr(r) > 1:
        r *= F(101, 100)
    q = r * h
    assert q < 1, f'step too long: r h = {float(q)}'
    out = []
    for d in cols:
        C = max(d[j].mag() / r ** j for j in range(m - 2, m + 2))
        v = sum((dn * F(h) ** n for n, dn in enumerate(d)), I(0))
        dv = sum((n * dn * F(h) ** (n - 1) for n, dn in enumerate(d) if n >= 1), I(0))
        tv = C * geo_sum(q, m + 2)
        td = C * r * geo_dsum(q, m + 2)
        out.append((v + I(-tv, tv), dv + I(-td, td), C, q))
    return out, Fr(r), r


def step_min(k, A, x0, L0, dL0, h, Nterms, pieces):
    """Lower bound of L on [x0, x0+h] by subdividing (positivity on the over side)."""
    mins = []
    for i in range(pieces):
        a, b = h * i / pieces, h * (i + 1) / pieces
        # value on [a,b] via the series at interval argument: reuse step_basis with interval h is costly;
        # use the end-point form: L(x0 + t) for t in [a, b] by series with interval t.
        res, _, _ = step_basis_interval(k, A, x0, I(a, b), Nterms)
        out = [(res[0][0], None), (res[1][0], None)]
        (La, _), (Lb, _) = out
        mins.append((La * L0 + Lb * dL0).lo)
    return min(mins)


def step_basis_interval(k, A, x0f, t, Nterms):
    x0 = I(x0f)
    N0 = 2 * R * x0 - k * x0 * x0 + A
    N1 = 2 * R - 2 * k * x0
    N2 = -k
    D = x0 * x0 - 1
    x0m = F(x0f)
    m = Nterms
    def Fr(r):
        return (2 * x0m / r + (1 + N0.mag() / ((m + 1) * (m + 2))) / r ** 2) / D.lo + \
               (N1.mag() / r ** 3 + N2.mag() / r ** 4) / (D.lo * (m + 1) * (m + 2))
    rr = (x0m + (2 * x0m * x0m - 1) ** 0.5) / (x0m * x0m - 1)
    r = F(rr).limit_denominator(1000) * F(1001, 1000)
    while Fr(r) > 1:
        r *= F(101, 100)
    q = r * t.hi
    res = []
    for init in ((I(1), I(0)), (I(0), I(1))):
        d = list(init)
        for n in range(Nterms):
            tt = 2 * x0 * (n + 1) ** 2 * d[n + 1] + (n * (n + 1) + N0) * d[n]
            if n >= 1:
                tt = tt + N1 * d[n - 1]
            if n >= 2:
                tt = tt + N2 * d[n - 2]
            d.append(-tt / (D * ((n + 1) * (n + 2))))
        C = max(d[j].mag() / r ** j for j in range(m - 2, m + 2))
        v = I(0)
        p = I(1)
        for dn in d:
            v = v + dn * p
            p = p * t
        tv = C * geo_sum(q, m + 2)
        res.append((v + I(-tv, tv), None))
    return res, Fr(r), r


def run(k1=F('2.20526842898'), k2=F('2.20526842900'), X=F(15)):
    # k1: E_total = 1/2 - k/2 = -0.60263421449, under side (L crosses zero);
    # k2: E_total = -0.60263421450, over side (L stays positive and grows).
    global tail_r
    log = []
    def say(*a):
        s = ' '.join(str(x) for x in a)
        print(s)
        log.append(s)
        sys.stdout.flush()

    # ---------------- eta: brackets of A at k1, k2
    tail_r = F(6, 10)
    Astar = {k1: F('0.8117295846'), k2: F('0.8117295846')}
    brackets = {}
    for k in (k1, k2):
        # find a narrow bracket by float-guided bisection over rationals
        lo, hi = Astar[k] - F(1, 10 ** 9), Astar[k] + F(1, 10 ** 9)
        def g(A):
            c, tail = eta_series(I(k), I(A))
            v, d = eval_series(c, tail, I(1))
            return d
        glo, ghi = g(lo), g(hi)
        assert glo.hi < 0 and ghi.lo > 0, (glo, ghi)
        for _ in range(40):
            mid = (lo + hi) / 2
            gm = g(mid)
            if gm.hi < 0:
                lo = mid
            elif gm.lo > 0:
                hi = mid
            else:
                break
        brackets[k] = (lo, hi)
        say(f'eta k={k}: A in [{float(lo):.20f}, {float(hi):.20f}] width {float(hi - lo):.3g}; '
            f'g(Al) <= {float(g(lo).hi):.3e} < 0 < g(Au) >= {float(g(hi).lo):.3e}')
    c, tail = eta_series(I(k1), I(brackets[k1][0]))
    say(f'eta tail induction F = {float(tail[0]):.6f} <= 1 (r = 6/10, M = {tail[2]})')

    # positivity of M on s in [0,1] over the box
    box_k = I(k1, k2)
    box_A = I(brackets[k1][0], brackets[k2][1])
    c, tail = eta_series(box_k, box_A)
    pieces = 16
    mmin = None
    for i in range(pieces):
        s = I(F(i, pieces), F(i + 1, pieces))
        v, _ = eval_series(c, tail, s)
        mmin = v.lo if mmin is None else min(mmin, v.lo)
    say(f'eta box k in [k1,k2], A in [{float(box_A.lo):.15f},{float(box_A.hi):.15f}]: min M on [0,1] >= {float(mmin):.6f}')

    # ---------------- xi shooting
    for k, side in ((k1, 'under'), (k2, 'over')):
        A = I(*brackets[k])
        kk = I(k)
        c, tail = xi_series(kk, A)
        say(f'xi {side} k={k}: Frobenius tail induction F = {float(tail[0]):.6f}')
        L, dL = eval_series(c, tail, I(1))
        x = F(2)
        Lmin = None
        if side == 'over':
            for i in range(8):
                v, _ = eval_series(c, tail, I(F(i, 8), F(i + 1, 8)))
                Lmin = v.lo if Lmin is None else min(Lmin, v.lo)
        nsteps = 0
        while x < X:
            h = min(F(1, 4) * x, X - x) if x >= 2 else F(1, 2)
            h = min(h, X - x)
            Nt = 120
            out, Fr, r = step_basis(kk, A, I(x), h, Nt)
            assert Fr <= 1
            (La, dLa, _, q), (Lb, dLb, _, _) = out
            if side == 'over' and x == 2:
                pm = step_min(kk, A, x, L, dL, h, Nt, 10)
                Lmin = min(Lmin, pm)
                say(f'  over: min L on [1, 5/2] >= {float(Lmin):.6e}; N(5/2) <= {float((2*R*I(F(5,2)) - kk*I(F(25,4)) + A).hi):.4f} < 0, '
                    f'5/2 past the vertex R/k; so L > 0 on [1, X] once L(X) > 0 (at most one zero where N < 0)')
            L, dL = La * L + Lb * dL, dLa * L + dLb * dL
            x += h
            nsteps += 1
            say(f'  x={float(x):.4f} (step {nsteps}, r h = {float(q):.3f}) L={L} dL={dL}')
        if side == 'under':
            say(f'UNDER at k1: L(X={X}) <= {float(L.hi):.6e} < 0: {L.hi < 0}')
        else:
            Nmax = (2 * R * I(X) - kk * I(X) * I(X) + A).hi
            vert = (2 * R / (2 * kk)).hi  # vertex of N; N decreasing past it
            say(f'OVER at k2: min L on [1,5/2] >= {float(Lmin):.6e} > 0: {Lmin > 0}; L(X) >= {float(L.lo):.6e} > 0: {L.lo > 0}; L\'(X) >= {float(dL.lo):.6e} > 0: {dL.lo > 0}; '
                f'N(X) <= {float(Nmax):.4f} < 0 and X past the vertex {float(vert):.4f}')
    return log


if __name__ == '__main__':
    if len(sys.argv) > 1:
        run(F(sys.argv[1]), F(sys.argv[2]), F(sys.argv[3]))
    else:
        run()
