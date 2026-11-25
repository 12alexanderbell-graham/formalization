"""Independent computation of the Bonnor-Ebert extrema xi_k (zeros of g = 2u - v)
and m(xi_k), using homology variables in t = log s, integrated with mpmath's
Taylor-series ODE solver at two working precisions / two start radii (error estimate)."""
import sys
import mpmath as mp
import sympy as sp

# series of w near 0 (verified by sympy)
S = sp.symbols('s')
cs = sp.symbols('c1:6')
wser = sum(c * S**(2 * (i + 1)) for i, c in enumerate(cs))
expr = sp.diff(wser, S, 2) + 2 / S * sp.diff(wser, S) + sp.exp(wser)
expr = sp.series(expr, S, 0, 10).removeO()
sol = sp.solve([sp.expand(expr).coeff(S, j) for j in range(0, 10, 2)], cs, dict=True)[0]
coef = [sol[c] for c in cs]
print("w series coeffs:", coef)


def run(dps, s0):
    mp.mp.dps = dps
    s0 = mp.mpf(s0)
    co = [mp.mpf(sp.Rational(c).p) / sp.Rational(c).q for c in coef]
    w = sum(co[i] * s0**(2 * (i + 1)) for i in range(5))
    wp = sum(co[i] * 2 * (i + 1) * s0**(2 * i + 1) for i in range(5))
    u0 = s0 * mp.e**w / (-wp)
    v0 = -s0 * wp
    t0 = mp.log(s0)
    f = mp.odefun(lambda t, y: [y[0] * (3 - y[0] - y[1]), y[1] * (y[0] - 1)], t0, [u0, v0])
    g = lambda t: 2 * f(t)[0] - f(t)[1]
    # scan for sign changes of g
    zeros = []
    t = t0
    h = mp.mpf('0.05')
    gp = g(t)
    while len(zeros) < 14:
        tn = t + h
        gn = g(tn)
        if gp * gn < 0:
            z = mp.findroot(g, (t, tn), solver='anderson')
            zeros.append(z)
        t, gp = tn, gn
    out = []
    c = mp.sqrt(2 / mp.pi)
    for z in zeros:
        u, v = f(z)
        m = mp.sqrt(u * v**3 / (4 * mp.pi))
        out.append((mp.e**z, m, u, v))
    # Nw at 300000
    u, v = f(mp.log(300000))
    Nw = 7 * (u - 1)**2 + ((u - 1) + 2 * (v - 2))**2
    return out, Nw


if __name__ == "__main__":
    A, NwA = run(40, '1e-4')
    B, NwB = run(30, '1e-5')
    mp.mp.dps = 40
    c = mp.sqrt(2 / mp.pi)
    print("Nw(300000) =", mp.nstr(NwA, 12), " (alt run:", mp.nstr(NwB, 12), ") bound 3.234e-5")
    for k, (a, b) in enumerate(zip(A, B)):
        xi, m, u, v = a
        print(f"k={k:2d} xi={mp.nstr(xi, 20):>28} m={mp.nstr(m, 20)} m-c={mp.nstr(m - c, 8)} "
              f"x=u-1={mp.nstr(u - 1, 8)} |dxi|rel={mp.nstr(abs(xi - b[0]) / xi, 3)} |dm|={mp.nstr(abs(m - b[1]), 3)} "
              f"chk m-c*u^2={mp.nstr(m - c * u**2, 3)}")
    print()
    print("quotients (k -> xi_{k+1}/xi_k, deviation quotient); distances to interval ends")
    for k in range(4, 12):
        r = A[k + 1][0] / A[k][0]
        d = (A[k + 1][1] - c) / (A[k][1] - c)
        rB = B[k + 1][0] / B[k][0]
        dB = (B[k + 1][1] - c) / (B[k][1] - c)
        print(f"k={k:2d} R={mp.nstr(r, 10)} (R-9.2={mp.nstr(r - 9.2, 5)}, 12.9-R={mp.nstr(12.9 - r, 5)}) "
              f"D={mp.nstr(d, 10)} (D+0.42={mp.nstr(d + mp.mpf('0.42'), 5)}, -0.21-D={mp.nstr(-mp.mpf('0.21') - d, 5)}) "
              f"alt-run diffs {mp.nstr(abs(r - rB), 3)}, {mp.nstr(abs(d - dB), 3)}")
    print("limits:", mp.nstr(mp.e**(2 * mp.pi / mp.sqrt(7)), 10), mp.nstr(-mp.e**(-mp.pi / mp.sqrt(7)), 10))
