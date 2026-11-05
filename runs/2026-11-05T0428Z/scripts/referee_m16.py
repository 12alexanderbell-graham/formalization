"""Referee recomputation for Work/Data/Moresco16.lean (Moresco et al. 2016, arXiv:1601.01701v2).
Independent of the screen scripts: table re-typed from the 200-dpi render of PDF p.18 (printed p.16).
Part 1: oLCDM best fit (mpmath, 40 digits), profiled over H0, on the prior wedge; line fit exact (Fractions);
        piecewise fit (float, several parameterisations); margins of the frozen numbers.
Run: python3 -I referee_m16.py"""
from fractions import Fraction as Fr
import mpmath as mp
import math
mp.mp.dps = 40

T4 = [("0.07","69.0","19.6"),("0.09","69","12"),("0.12","68.6","26.2"),("0.17","83","8"),("0.179","75","4"),
      ("0.199","75","5"),("0.20","72.9","29.6"),("0.27","77","14"),("0.28","88.8","36.6"),("0.352","83","14"),
      ("0.3802","83","13.5"),("0.4","95","17"),("0.4004","77","10.2"),("0.4247","87.1","11.2"),("0.44497","92.8","12.9"),
      ("0.4783","80.9","9"),("0.48","97","62"),("0.593","104","13"),("0.68","92","8"),("0.781","105","12"),
      ("0.875","125","17"),("0.88","90","40"),("0.9","117","23"),("1.037","154","20"),("1.3","168","17"),
      ("1.363","160","33.6"),("1.43","177","18"),("1.53","140","14"),("1.75","202","40"),("1.965","186.5","50.4")]
assert len(T4) == 30

def table(fix_typo=False):
    rows = list(T4)
    if fix_typo:
        rows[14] = ("0.4497",) + rows[14][1:]
    return rows

# ---------------- oLCDM ----------------
def e2(Om, OL, z):
    return Om*(1+z)**3 + (1-Om-OL)*(1+z)**2 + OL

def abg(Om, OL, rows, H0p=mp.mpf(73), sp=mp.mpf('2.4')):
    al = 1/sp**2; be = H0p/sp**2; ga = H0p**2/sp**2
    for z, H, s in rows:
        z, H, s = mp.mpf(z), mp.mpf(H), mp.mpf(s)
        E2 = e2(Om, OL, z)
        if E2 <= 0: return None
        w = 1/s**2; al += E2*w; be += mp.sqrt(E2)*H*w; ga += H**2*w
    return al, be, ga

def Fprof(Om, OL, rows, **kw):
    r = abg(Om, OL, rows, **kw)
    if r is None: return mp.inf
    al, be, ga = r
    return ga - be**2/al

def chi2_full(H0, Om, OL, rows, H0p=73, sp='2.4'):
    s = sum((H0*mp.sqrt(e2(Om, OL, mp.mpf(z))) - mp.mpf(H))**2/mp.mpf(sig)**2 for z, H, sig in rows)
    return s + (H0 - mp.mpf(H0p))**2/mp.mpf(sp)**2

def olcdm_min(rows, x0=(mp.mpf('0.436'), mp.mpf('0.981')), **kw):
    f = lambda a, b: Fprof(a, b, rows, **kw)
    gx = lambda a, b: mp.diff(f, (a, b), (1, 0))
    gy = lambda a, b: mp.diff(f, (a, b), (0, 1))
    sol = mp.findroot([gx, gy], x0)
    Om, OL = sol[0], sol[1]
    al, be, ga = abg(Om, OL, rows, **kw)
    return Om, OL, be/al, f(Om, OL)

def grid_scan(rows, n1=400, n2=400):
    """float scan of the wedge 0<=Om<=1, Om<=2OL<=15.625 Om (z_t in [0,1.5]), parameterised by (Om, z_t)."""
    best = (1e9, None)
    for i in range(1, n1+1):
        Om = i/n1
        for j in range(n2+1):
            zt = 1.5*j/n2
            OL = Om*(1+zt)**3/2
            ok = True; al = 1/5.76; be = 73/5.76; ga = 73**2/5.76
            for z, H, s in rows:
                z, H, s = float(z), float(H), float(s)
                E2 = e2(Om, OL, z)
                if E2 <= 0: ok = False; break
                w = 1/s**2; al += E2*w; be += math.sqrt(E2)*H*w; ga += H*H*w
            if ok:
                F = ga - be*be/al
                if F < best[0]: best = (F, (Om, zt, OL))
    return best

# ---------------- line (exact) ----------------
def line_fit(rows, with_H0=True, sigma_div=True, fit_H=False):
    pts = []
    if with_H0: pts.append((Fr(0), Fr(73), Fr('2.4')))
    for z, H, s in rows:
        z, H, s = Fr(z), Fr(H), Fr(s)
        if fit_H: pts.append((z, H, s))
        else: pts.append((z, H/(1+z), s/(1+z) if sigma_div else s))
    S=Sx=Sxx=Sy=Sxy=Syy=Fr(0)
    for x, y, s in pts:
        w = 1/s**2; S+=w; Sx+=w*x; Sxx+=w*x*x; Sy+=w*y; Sxy+=w*x*y; Syy+=w*y*y
    D = S*Sxx - Sx**2
    a = (Sxx*Sy - Sx*Sxy)/D; b = (S*Sxy - Sx*Sy)/D
    return a, b, Syy - a*Sy - b*Sxy, len(pts)

# ---------------- piecewise (float) ----------------
def wls(X, y, w):
    import numpy as np
    X = np.asarray(X); y = np.asarray(y); w = np.asarray(w)
    A = X.T @ (X*w[:, None]); bb = X.T @ (y*w)
    p = np.linalg.solve(A, bb); r = y - X @ p
    return p, float((r*r*w).sum())

def piecewise(rows, zt_grid, with_H0=True, continuous=True):
    xs = [0.0] if with_H0 else []; ys = [73.0] if with_H0 else []; ss = [2.4] if with_H0 else []
    for z, H, s in rows:
        z, H, s = float(z), float(H), float(s); xs.append(z); ys.append(H/(1+z)); ss.append(s/(1+z))
    w = [1/s**2 for s in ss]
    best = (1e9, None)
    for zt in zt_grid:
        if continuous:
            X = [[1.0, min(x-zt, 0.0), max(x-zt, 0.0)] for x in xs]
        else:  # two independent lines meeting nowhere (5 params incl zt)
            X = [[1.0, x, 0, 0] if x < zt else [0, 0, 1.0, x] for x in xs]
        try:
            p, c = wls(X, ys, w)
        except Exception:
            continue
        if c < best[0]: best = (c, zt)
    return best

if __name__ == '__main__':
    rows = table()
    Om, OL, H0, F = olcdm_min(rows)
    zt = mp.cbrt(2*OL/Om) - 1
    print('oLCDM (printed table): Om*=%s OL*=%s H0*=%s' % (mp.nstr(Om, 12), mp.nstr(OL, 12), mp.nstr(H0, 12)))
    print('   chi2min = %s   z_t* = %s   2OL/Om = %s' % (mp.nstr(F, 20), mp.nstr(zt, 10), mp.nstr(2*OL/Om, 10)))
    print('   check full chi2 at (H0*,Om*,OL*) =', mp.nstr(chi2_full(H0, Om, OL, rows), 20))
    print('   min E2 over table at optimum =', mp.nstr(min(e2(Om, OL, mp.mpf(z)) for z, _, _ in rows), 8))
    # a rational witness (as a prover would use) and its chi2
    w = (mp.mpf('72.2865'), mp.mpf('0.4362'), mp.mpf('0.9814'))
    cw = chi2_full(*w, rows)
    print('   witness (72.2865,0.4362,0.9814): chi2 =', mp.nstr(cw, 15), ' margin to 14.975:', mp.nstr(14.975-cw, 6),
          '; +3 ln 35 =', mp.nstr(cw+3*mp.log(35), 10), ' margin to 25.705:', mp.nstr(25.705-cw-3*mp.log(35), 6))
    Fg = grid_scan(rows, 200, 200)
    print('   grid scan of wedge (Om in (0,1], z_t in [0,1.5]) min F =', round(Fg[0], 6), 'at', tuple(round(v, 4) for v in Fg[1]))
    Om2, OL2, H02, F2 = olcdm_min(table(True))
    print('   with z=0.4497 typo fixed: chi2min =', mp.nstr(F2, 12))
    for N in (30, 31):
        print('   N=%d: AICc=%.4f AIC=%.4f BIC=%.4f  (printed 21.41 / 25.71)' % (N, float(F)+6+24/(N-4), float(F)+6, float(F)+3*math.log(N)))

    a, b, c, n = line_fit(rows)
    print('\nline (31 pts incl H0=73+-2.4, sigma_f=sigma_H/(1+z)): a=%.8f b=%.8f chi2min=%.12f n=%d' % (float(a), float(b), float(c), n))
    print('   margin to 27.972: %.6f; chi2+2ln35 = %.6f (bound 35.285)' % (27.972-float(c), float(c)+2*math.log(35)))
    for N in (30, 31):
        print('   N=%d: AICc=%.4f AIC=%.4f BIC=%.4f  (printed 32.42 / 35.29)' % (N, float(c)+4+12/(N-3), float(c)+4, float(c)+2*math.log(N)))
    for lab, kw in (('30 pts, no H0', dict(with_H0=False)), ('sigma_f=sigma_H (not divided)', dict(sigma_div=False)),
                    ('fit H(z) itself, +H0 pt', dict(fit_H=True)), ('typo fixed', {})):
        r = table(True) if lab == 'typo fixed' else rows
        a2, b2, c2, n2 = line_fit(r, **kw)
        print('   variant %-30s chi2=%.4f (n=%d)' % (lab, float(c2), n2))

    g = [i/2000 for i in range(1, 4001)]
    for lab, kw in (('continuous, +H0 pt, z_t in (0,2]', {}), ('continuous, no H0 pt', dict(with_H0=False))):
        cbest, ztb = piecewise(rows, g, **kw)
        print('\npiecewise %s: chi2min=%.5f at z_t=%.4f; k=4 N=31: AICc=%.3f BIC=%.3f AIC=%.3f (printed 23.99/28.72)' % (
            lab, cbest, ztb, cbest+8+40/26, cbest+4*math.log(31), cbest+8))
    cb, zb = piecewise(rows, [i/2000 for i in range(1, 3001)], continuous=False)
    print('piecewise discontinuous (two free lines, k=5): chi2min=%.5f at z_t=%.4f' % (cb, zb))
    cb, zb = piecewise(rows, [i/2000 for i in range(1, 3001)])
    print('piecewise continuous restricted z_t in (0,1.5]: chi2min=%.5f at z_t=%.4f' % (cb, zb))
