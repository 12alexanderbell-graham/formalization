"""Float scan of s=f''(0) in [-3,3] for fast-approach solutions (Robin far-field residual sign changes), with sup|f'|."""
import numpy as np
from scipy.integrate import solve_ivp
def rhs(t, y, b): f, p, q = y; return [p, q, -f*q - b*(1 - p*p)]
def blow(t, y, b): return abs(y[1]) - 5
blow.terminal = True
def run(s, b, L=12.0):
    sol = solve_ivp(rhs, [0, L], [0, 0, s], args=(b,), rtol=1e-11, atol=1e-13, events=blow, dense_output=False, max_step=0.05)
    f, p, q = sol.y[:, -1]
    if sol.t[-1] < L: return None, sol.y[1].min(), sol.y[1].max()
    r = q - (1 - p)*(f + (1 + 2*b)/f)
    return r, sol.y[1].min(), sol.y[1].max()
import sys
for b in [float(a) for a in sys.argv[1:]] or [-0.15, -0.17, -0.18, -0.19]:
    S = np.linspace(-3, 3, 3001)
    R = [run(s, b) for s in S]
    roots = []
    for i in range(len(S) - 1):
        r0, r1 = R[i][0], R[i+1][0]
        if r0 is not None and r1 is not None and np.sign(r0) != np.sign(r1):
            lo, hi = S[i], S[i+1]
            for _ in range(50):
                m = 0.5*(lo + hi); rm = run(m, b)[0]
                if rm is None: break
                if np.sign(rm) == np.sign(run(lo, b)[0]): lo = m
                else: hi = m
            r, pmin, pmax = run(0.5*(lo + hi), b, L=12.0)
            roots.append((0.5*(lo + hi), pmin, pmax))
    print(b, 'roots:', [('%.10f' % s, 'pmin=%.4f' % a, 'pmax=%.6f' % c) for s, a, c in roots])
    print('   reaching L without blowup: s in', S[[r[0] is not None for r in R]].min(), S[[r[0] is not None for r in R]].max(), 'count', sum(r[0] is not None for r in R))
