# Method B: mpmath.odefun (adaptive Taylor) started at x0 = 0.25 from the centre series
# w = sum c_k x^k computed independently via sympy-free power-series recurrence for (x^2 w')' = -x^2 e^w.
# Plus Method C: scipy DOP853 in double precision (sanity check only).
import mpmath as mp
mp.mp.dps = 40

# centre series in t = x^2: w = sum a_n t^n ; e^w = sum b_n t^n.
# (x^2 w')' = -x^2 e^w  =>  sum 2n(2n+1) a_n t^{n} = -sum b_{n-1} t^{n}   => a_n = -b_{n-1}/(2n(2n+1))
def centre(x0, K=80):
    a = [mp.mpf(0)] * (K + 1); b = [mp.mpf(1)] + [mp.mpf(0)] * K
    for n in range(1, K + 1):
        a[n] = -b[n - 1] / (2 * n * (2 * n + 1))
        b[n] = sum(j * a[j] * b[n - j] for j in range(1, n + 1)) / n
    t = mp.mpf(x0) ** 2
    W = sum(a[n] * t ** n for n in range(K + 1))
    P = sum(2 * n * a[n] * mp.mpf(x0) ** (2 * n - 1) for n in range(1, K + 1))
    return W, P, a

x0 = mp.mpf('0.25')
W0, P0, a = centre(x0)
print('series coeffs a1..a3:', [mp.nstr(c, 12) for c in a[1:4]], '(expect -1/6, 1/120, -1/1890)')
sol = mp.odefun(lambda x, y: [y[1], -2 * y[1] / x - mp.e ** y[0]], x0, [W0, P0])

def F(x):
    W, P = sol(x)
    return mp.e ** W - P ** 2 / 2

xi = mp.findroot(F, mp.mpf('6.4507'), tol=mp.mpf(10) ** -32)
W, P = sol(xi)
m = xi ** 2 * (-P) * mp.e ** (W / 2) / mp.sqrt(4 * mp.pi)
print('xi1      =', mp.nstr(xi, 28))
print('m(xi1)   =', mp.nstr(m, 28))
print('contrast =', mp.nstr(mp.e ** (-W), 28))
# closed-form check of dm/dx against numerical derivative of m at a test point
def mfun(x):
    W, P = sol(x); return x ** 2 * (-P) * mp.e ** (W / 2) / mp.sqrt(4 * mp.pi)
xt = mp.mpf(3)
W, P = sol(xt)
print('dm/dx numeric vs closed form at 3:', mp.nstr(mp.diff(mfun, xt), 15),
      mp.nstr(xt ** 2 * mp.e ** (W / 2) * (mp.e ** W - P ** 2 / 2) / mp.sqrt(4 * mp.pi), 15))

try:
    import numpy as np
    from scipy.integrate import solve_ivp
    from scipy.optimize import brentq
    x0f = 1e-3
    y0 = [-x0f ** 2 / 6 + x0f ** 4 / 120, -x0f / 3 + x0f ** 3 / 30]
    s = solve_ivp(lambda x, y: [y[1], -2 * y[1] / x - np.exp(y[0])], [x0f, 7], y0, method='DOP853',
                  rtol=1e-13, atol=1e-15, dense_output=True)
    Ff = lambda x: np.exp(s.sol(x)[0]) - s.sol(x)[1] ** 2 / 2
    r = brentq(Ff, 6, 7, xtol=1e-15)
    Wf, Pf = s.sol(r)
    print('DOP853: xi1 = %.15f  m = %.15f  contrast = %.15f' % (r, r * r * (-Pf) * np.exp(Wf / 2) / np.sqrt(4 * np.pi), np.exp(-Wf)))
except Exception as e:
    print('scipy check failed', e)
