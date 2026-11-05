"""Screen: Farooq, Madiyar, Crandall & Ratra 2017 (arXiv:1607.03537), Table 1 (38 H(z), p.2) and Table 3 (p.8).
Non-flat LCDM: E^2 = Om(1+z)^3 + OL + (1-Om-OL)(1+z)^2  (linear in (Om, OL)).
Statistic (FMR13 Eq.16 / FR13 frozen convention): F(p) = -2 ln int_R exp(-chi2/2) N(H0; Hbar, sH) dH0
  = gamma - beta^2/alpha + ln(alpha sH^2),  alpha = 1/sH^2 + sum E^2 w, beta = Hbar/sH^2 + sum E H w,
  gamma = Hbar^2/sH^2 + sum H^2 w   (diagonal case; with a covariance C, w-sums become E^T C^-1 E etc.).
Also the flat-LCDM restriction OL = 1 - Om.
"""
import numpy as np
from scipy.optimize import minimize

T1 = [  # z, H, sigma  (Table 1 as printed)
    (0.070, 69, 19.6), (0.090, 69, 12), (0.120, 68.6, 26.2), (0.170, 83, 8), (0.179, 75, 4),
    (0.199, 75, 5), (0.200, 72.9, 29.6), (0.270, 77, 14), (0.280, 88.8, 36.6), (0.352, 83, 14),
    (0.380, 81.5, 1.9), (0.3802, 83, 13.5), (0.400, 95, 17), (0.4004, 77, 10.2), (0.4247, 87.1, 11.2),
    (0.440, 82.6, 7.8), (0.4497, 92.8, 12.9), (0.4783, 80.9, 9), (0.480, 97, 62), (0.510, 90.4, 1.9),
    (0.593, 104, 13), (0.600, 87.9, 6.1), (0.610, 97.3, 2.1), (0.680, 92, 8), (0.730, 97.3, 7),
    (0.781, 105, 12), (0.875, 125, 17), (0.880, 90, 40), (0.900, 117, 23), (1.037, 154, 20),
    (1.300, 168, 17), (1.363, 160, 33.6), (1.430, 177, 18), (1.530, 140, 14), (1.750, 202, 40),
    (1.965, 186.5, 50.4), (2.340, 222, 7), (2.360, 226, 8),
]
PRIORS = {'68': (68.0, 2.8), '73.24': (73.24, 1.74)}
PRINTED = {'68': (0.23, 0.60, 22.4), '73.24': (0.25, 0.78, 24.2)}

z = np.array([r[0] for r in T1]); H = np.array([r[1] for r in T1], float); s = np.array([r[2] for r in T1], float)


def cov(alam=False, blake_r=None):
    C = np.diag(s**2)
    if alam:  # correlation pattern of Alam et al. covariance (Yu, Ratra & Wang 2018 Eq.1)
        A = np.array([[3.65, 1.78, 0.93], [1.78, 3.65, 2.20], [0.93, 2.20, 4.45]])
        R = A / np.sqrt(np.outer(np.diag(A), np.diag(A)))
        idx = [10, 19, 22]
        for a in range(3):
            for b in range(3):
                C[idx[a], idx[b]] = R[a, b] * s[idx[a]] * s[idx[b]]
    if blake_r is not None:  # hypothetical adjacent-bin correlation for WiggleZ H(z)
        idx = [15, 21, 24]
        for a, b in ((0, 1), (1, 2)):
            C[idx[a], idx[b]] = C[idx[b], idx[a]] = blake_r * s[idx[a]] * s[idx[b]]
    return np.linalg.inv(C)


def F(p, Ci, prior, flat=False):
    Om, OL = (p[0], 1 - p[0]) if flat else p
    E2 = Om * (1 + z)**3 + OL + (1 - Om - OL) * (1 + z)**2
    if np.any(E2 <= 0):
        return 1e9
    E = np.sqrt(E2); Hb, sH = prior
    al = 1 / sH**2 + E @ Ci @ E; be = Hb / sH**2 + E @ Ci @ H; ga = Hb**2 / sH**2 + H @ Ci @ H
    return ga - be**2 / al + np.log(al * sH**2)


def fit(Ci, prior, flat=False):
    if flat:
        g = np.linspace(0, 1, 2001); v = [F([x], Ci, prior, True) for x in g]
        r = minimize(lambda p: F(p, Ci, prior, True), [g[int(np.argmin(v))]], method='Nelder-Mead',
                     options={'xatol': 1e-12, 'fatol': 1e-13})
        return r.x, r.fun
    best = None
    for a in np.linspace(0.05, 0.6, 6):
        for b in np.linspace(0.2, 1.2, 6):
            r = minimize(lambda p: F(p, Ci, prior), [a, b], method='Nelder-Mead',
                         options={'xatol': 1e-12, 'fatol': 1e-13, 'maxiter': 10000})
            if best is None or r.fun < best.fun:
                best = r
    return best.x, best.fun


def zda_lcdm(Om, OL):
    return (2 * OL / Om)**(1 / 3) - 1


if __name__ == '__main__':
    for label, Ci in (('diag', cov()), ('alam', cov(alam=True)),
                      ('alam+blake0.4', cov(alam=True, blake_r=0.4))):
        for k, pr in PRIORS.items():
            p, f = fit(Ci, pr)
            # grid min on the paper's 0.01 grid
            gs = [(F([a, b], Ci, pr), a, b) for a in np.arange(0.0, 1.0001, 0.01) for b in np.arange(0.0, 1.6001, 0.01)]
            gmin = min(gs)
            pf, ff = fit(Ci, pr, flat=True)
            print(f'{label:14s} h={k:5s} nonflat BF Om={p[0]:.5f} OL={p[1]:.5f} F={f:.4f} zda={zda_lcdm(*p):.4f}'
                  f' | 0.01-grid ({gmin[1]:.2f},{gmin[2]:.2f}) F={gmin[0]:.4f} | printed {PRINTED[k]}'
                  f' | flat Om={pf[0]:.6f} F={ff:.6f}')
