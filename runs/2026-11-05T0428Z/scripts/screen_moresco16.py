"""Screen: Moresco et al. 2016 (arXiv:1601.01701v2), Table 4 (p.16 printed / PDF p.18), Table 5 (PDF p.20).
Reproduce chi2_min / AICc / BIC of Table 5 for (i) oLCDM, (ii) piecewise-linear H/(1+z), (iii) straight line.
All fits use the Gaussian H0 prior 73 +- 2.4 (as a z=0 point for the f = H/(1+z) fits).
"""
import numpy as np
from scipy.optimize import minimize, minimize_scalar

# Table 4 exactly as printed (z, H, sigma). NB: printed z '0.44497' is a typo for 0.4497 (Moresco 2016 Table 1).
T4 = [
    (0.07, 69.0, 19.6), (0.09, 69, 12), (0.12, 68.6, 26.2), (0.17, 83, 8), (0.179, 75, 4),
    (0.199, 75, 5), (0.20, 72.9, 29.6), (0.27, 77, 14), (0.28, 88.8, 36.6), (0.352, 83, 14),
    (0.3802, 83, 13.5), (0.4, 95, 17), (0.4004, 77, 10.2), (0.4247, 87.1, 11.2), (0.44497, 92.8, 12.9),
    (0.4783, 80.9, 9), (0.48, 97, 62), (0.593, 104, 13), (0.68, 92, 8), (0.781, 105, 12),
    (0.875, 125, 17), (0.88, 90, 40), (0.9, 117, 23), (1.037, 154, 20), (1.3, 168, 17),
    (1.363, 160, 33.6), (1.43, 177, 18), (1.53, 140, 14), (1.75, 202, 40), (1.965, 186.5, 50.4),
]
H0P, SH0P = 73.0, 2.4


def arrays(fix_typo=False):
    z = np.array([r[0] for r in T4]); H = np.array([r[1] for r in T4], float); s = np.array([r[2] for r in T4], float)
    if fix_typo:
        z = np.where(np.isclose(z, 0.44497), 0.4497, z)
    return z, H, s


def wls(X, y, s):
    W = 1 / s**2
    A = X.T @ (X * W[:, None]); b = X.T @ (y * W)
    p = np.linalg.solve(A, b)
    r = (X @ p - y) / s
    return p, float(r @ r)


def f_data(fix_typo=False):
    z, H, s = arrays(fix_typo)
    zz = np.concatenate([[0.0], z]); f = np.concatenate([[H0P], H / (1 + z)]); sf = np.concatenate([[SH0P], s / (1 + z)])
    return zz, f, sf


def line(fix_typo=False):
    zz, f, sf = f_data(fix_typo)
    X = np.stack([np.ones_like(zz), zz], 1)
    return wls(X, f, sf)


def piecewise(fix_typo=False, zt_range=(0.005, 1.96)):
    zz, f, sf = f_data(fix_typo)
    def c2(zt):
        X = np.stack([np.ones_like(zz), np.minimum(zz - zt, 0), np.maximum(zz - zt, 0)], 1)
        return wls(X, f, sf)[1]
    grid = np.linspace(*zt_range, 20001)
    v = np.array([c2(t) for t in grid])
    i = int(np.argmin(v))
    r = minimize_scalar(c2, bounds=(grid[max(i - 2, 0)], grid[min(i + 2, len(grid) - 1)]), method='bounded',
                        options={'xatol': 1e-12})
    return r.x, r.fun, grid, v


def olcdm_chi2(p, z, H, s):
    H0, Om, OL = p
    Ok = 1 - Om - OL
    E2 = Om * (1 + z)**3 + Ok * (1 + z)**2 + OL
    if np.any(E2 <= 0):
        return 1e9
    return float(np.sum(((H0 * np.sqrt(E2) - H) / s)**2) + ((H0 - H0P) / SH0P)**2)


def olcdm(fix_typo=False, bounded=True):
    z, H, s = arrays(fix_typo)
    best = None
    for Om0 in np.linspace(0.05, 0.95, 10):
        for OL0 in np.linspace(0.0, 1.5, 10):
            r = minimize(olcdm_chi2, [70, Om0, OL0], args=(z, H, s), method='Nelder-Mead',
                         options={'xatol': 1e-10, 'fatol': 1e-12, 'maxiter': 20000})
            H0, Om, OL = r.x
            if bounded:
                zt = (2 * OL / Om)**(1 / 3) - 1 if Om > 0 and OL > 0 else np.nan
                if not (0 <= Om <= 1 and 0 <= zt <= 1.5):
                    continue
            if best is None or r.fun < best.fun:
                best = r
    return best


def ic(chi2, k, N):
    return chi2 + 2 * k + 2 * k * (k + 1) / (N - k - 1), chi2 + k * np.log(N)


if __name__ == '__main__':
    printed = {'oLCDM': (21.41, 25.71), 'piecewise': (23.99, 28.72), 'line': (32.42, 35.29)}
    for fix in (False, True):
        print(f'=== fix_typo={fix}')
        p, c = line(fix); print('line: params', p, 'chi2min', c)
        zt, cp, g, v = piecewise(fix); print('piecewise: zt*', zt, 'chi2min', cp)
        b = olcdm(fix); H0, Om, OL = b.x; zt_l = (2 * OL / Om)**(1 / 3) - 1
        print('oLCDM: H0 Om OL', b.x, 'zt', zt_l, 'chi2min', b.fun)
        for name, chi, k in (('oLCDM', b.fun, 3), ('piecewise', cp, 4), ('line', c, 2)):
            for N in (30, 31):
                a_, bi = ic(chi, k, N)
                print(f'  {name:9s} k={k} N={N}: AICc={a_:.2f} BIC={bi:.2f}   printed {printed[name]}')
            # implied chi2 from printed values
            pa, pb = printed[name]
            print(f'  {name:9s} implied chi2 from printed AICc (k={k},N=31): {pa - 2*k - 2*k*(k+1)/(31-k-1):.3f};'
                  f' from printed BIC: {pb - k*np.log(31):.3f}')
    # piecewise Delta-chi2 profile (68% / 95%)
    zt, cp, g, v = piecewise(False)
    for lev, d in (('68%', 1.0), ('95%', 4.0), ('99.7%', 9.0)):
        ok = g[v <= cp + d]; print('piecewise profile', lev, ok.min(), ok.max())


# ---------- extra checks (appended) ----------
def prof_H0(Om, OL, z, H, s):
    """oLCDM chi2 profiled analytically over H0 (prior term included): gamma - beta^2/alpha."""
    E2 = Om * (1 + z)**3 + (1 - Om - OL) * (1 + z)**2 + OL
    if np.any(E2 <= 0):
        return np.inf, np.nan
    E = np.sqrt(E2); w = 1 / s**2
    al = 1 / SH0P**2 + np.sum(E2 * w); be = H0P / SH0P**2 + np.sum(E * H * w); ga = H0P**2 / SH0P**2 + np.sum(H**2 * w)
    return ga - be**2 / al, al


def zt_posteriors():
    z, H, s = arrays(False)
    oms = np.linspace(0.0005, 0.9995, 1000); zts = np.linspace(0.0, 1.5, 1501)
    P = np.zeros((len(zts), len(oms))); Q = np.zeros_like(P); prof = np.full(len(zts), np.inf)
    for i, t in enumerate(zts):
        for j, om in enumerate(oms):
            OL = om * (1 + t)**3 / 2
            c, al = prof_H0(om, OL, z, H, s)
            if np.isfinite(c):
                P[i, j] = np.exp(-(c - 14.0) / 2) / np.sqrt(al)  # H0 marginalised (Gaussian integral)
                Q[i, j] = np.exp(-(c - 14.0) / 2)             # H0 profiled
                prof[i] = min(prof[i], c)
    for name, M in (('H0-marg', P), ('H0-prof', Q)):
        m = M.sum(1); m /= m.sum(); cdf = np.cumsum(m)
        med = zts[np.searchsorted(cdf, 0.5)]; lo = zts[np.searchsorted(cdf, 0.16)]; hi = zts[np.searchsorted(cdf, 0.84)]
        mode = zts[np.argmax(m)]
        print(f'oLCDM zt marginal ({name}, uniform Om in[0,1], zt in [0,1.5]): mode {mode:.3f} median {med:.3f} 68% [{lo:.3f},{hi:.3f}]')
    ok = zts[prof <= prof.min() + 1]; print('oLCDM zt profile chi2: min', prof.min(), 'at', zts[np.argmin(prof)], ' dchi2<1:', ok.min(), ok.max())
    ok9 = zts[prof <= prof.min() + 9]; print('   dchi2<9:', ok9.min(), ok9.max())


def global_olcdm():
    z, H, s = arrays(False)
    best = None
    for a in np.linspace(0.05, 1.5, 12):
        for b in np.linspace(-0.5, 2.0, 12):
            r = minimize(lambda p: prof_H0(p[0], p[1], z, H, s)[0], [a, b], method='Nelder-Mead',
                         options={'xatol': 1e-12, 'fatol': 1e-13, 'maxiter': 20000})
            if np.isfinite(r.fun) and (best is None or r.fun < best.fun):
                best = r
    Om, OL = best.x
    print('global (unconstrained) profiled oLCDM min:', best.x, best.fun, 'zt', (2 * OL / Om)**(1 / 3) - 1)


def pw_marginal():
    zz, f, sf = f_data(False)
    g = np.linspace(0.01, 1.95, 3881); lp = []
    for t in g:
        X = np.stack([np.ones_like(zz), np.minimum(zz - t, 0), np.maximum(zz - t, 0)], 1)
        W = 1 / sf**2; A = X.T @ (X * W[:, None]); p = np.linalg.solve(A, X.T @ (f * W)); r = (X @ p - f) / sf
        lp.append(-(r @ r) / 2 - 0.5 * np.linalg.slogdet(A)[1])
    lp = np.array(lp); m = np.exp(lp - lp.max()); m /= m.sum(); cdf = np.cumsum(m)
    print('piecewise zt marginal (flat priors on linear params): mode %.3f median %.3f 68%% [%.3f, %.3f]' % (
        g[np.argmax(m)], g[np.searchsorted(cdf, .5)], g[np.searchsorted(cdf, .16)], g[np.searchsorted(cdf, .84)]))


if __name__ == '__main__':
    global_olcdm(); zt_posteriors(); pw_marginal()
