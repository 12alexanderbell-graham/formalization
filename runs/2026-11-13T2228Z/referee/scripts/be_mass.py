"""Independent referee computation: Bonnor-Ebert mass curve, extrema, Lyapunov function.

Conventions: psi'' + (2/x) psi' = exp(-psi), psi(0)=psi'(0)=0  (w = -psi).
m(x) = x^2 psi'(x) exp(-psi/2) / sqrt(4 pi).
Homology variables u = x e^{-psi}/psi', v = x psi', t = log x:
  du/dt = u(3-u-v), dv/dt = v(u-1);  4 pi m^2 = u v^3.
"""
import sys
import mpmath as mp

mp.mp.dps = 30

# --- power series of psi about 0 (exact recursion), used to start away from the singular point
# psi = sum a_k x^{2k}; e^{-psi} = sum b_k x^{2k}; (2k+2)(2k+3) a_{k+1} = b_k
def series_coeffs(N):
    a = [mp.mpf(0)] * (N + 1)
    b = [mp.mpf(0)] * (N + 1)
    # e^{-psi}: E' = -psi' E  -> coefficient recursion in y = x^2: E = sum b_k y^k, psi = sum a_k y^k
    # dE/dy = -dpsi/dy * E: (k+1) b_{k+1} = -sum_{j=0}^{k} (j+1) a_{j+1} b_{k-j}
    b[0] = mp.mpf(1)
    a[0] = mp.mpf(0)
    for k in range(N):
        a[k + 1] = b[k] / ((2 * k + 2) * (2 * k + 3))
        s = mp.mpf(0)
        for j in range(k + 1):
            s += (j + 1) * a[j + 1] * b[k - j]
        b[k + 1] = -s / (k + 1)
    return a

A = series_coeffs(60)

def psi_series(x):
    y = x * x
    p = mp.mpf(0); dp = mp.mpf(0)
    for k in range(len(A) - 1, -1, -1):
        p = p * y + A[k]
    for k in range(len(A) - 1, 0, -1):
        dp = dp * y + 2 * k * A[k]
    return p, dp * x  # psi, psi'

# --- integrate psi in x with mpmath taylor ODE solver from x0 to x1 (for the [x0, 12] range)
x0 = mp.mpf('0.5')
p0, dp0 = psi_series(x0)

f_x = mp.odefun(lambda x, Y: [Y[1], mp.exp(-Y[0]) - 2 * Y[1] / x], x0, [p0, dp0])

def mass_x(x):
    if x <= x0:
        p, dp = psi_series(x)
    else:
        p, dp = f_x(x)
    return x * x * dp * mp.exp(-p / 2) / mp.sqrt(4 * mp.pi)

def uv_x(x):
    if x <= x0:
        p, dp = psi_series(x)
    else:
        p, dp = f_x(x)
    return x * mp.exp(-p) / dp, x * dp

if __name__ == '__main__':
    # first maximum: dm/dx = 0 <-> v = 2u
    g = lambda x: (lambda uv: uv[1] - 2 * uv[0])(uv_x(x))
    xi1 = mp.findroot(g, mp.mpf('6.45'))
    m1 = mass_x(xi1)
    print('xi1 =', mp.nstr(xi1, 20))
    print('m(xi1) =', mp.nstr(m1, 20))
    print('4 pi m1^2 =', mp.nstr(4 * mp.pi * m1 ** 2, 20))
    u7, v7 = uv_x(mp.mpf(7))
    V = lambda u, v: (u - 1 - mp.log(u)) + (v - 2 - 2 * mp.log(v / 2))
    print('u(7), v(7) =', mp.nstr(u7, 20), mp.nstr(v7, 20))
    print('m(7) =', mp.nstr(mass_x(7), 20))
    print('V(7) =', mp.nstr(V(u7, v7), 20))
    # cross-check the series at x0 against the ODE slightly beyond
    print('series vs ode at 0.5:', mp.nstr(psi_series(mp.mpf('0.5'))[0] - f_x(mp.mpf('0.5'))[0], 5))
