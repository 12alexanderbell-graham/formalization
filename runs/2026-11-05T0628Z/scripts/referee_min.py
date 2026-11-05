"""Referee (run 2026-11-05T0628Z) for Work/Data/Moresco16Min.lean: independent global minimum of the
open-LCDM chi^2 of Moresco et al. 2016 (arXiv:1601.01701v2) Table 4 with prior H0 = 73 +- 2.4.

Independent of the program's scripts (feas_wide.py / opt_float.py): own data entry (decimal strings),
own enclosure method (natural interval + centred mean-value form, bisection), own mpmath refinement.

chi^2(H0, m, l) = sum w_i (H0 sqrt(y_i) - H_i)^2 + w0 (H0 - 73)^2,  y_i = m(1+z)^3 + (1-m-l)(1+z)^2 + l.
For fixed (m, l) it is a quadratic in H0 with leading coefficient alpha > 0, so
inf_H0 chi^2 = F(m, l) = gamma - beta^2/alpha (attained at H0 = beta/alpha).

Part A: branch and bound over the WIDE region {m <= 1, l >= 0, all y_i >= 0}, proving (in floats with a
        1e-6 safety margin) F >= 14.9665 everywhere, and localising all points with F < 14.968.
Part B: 50-digit mpmath refinement of the minimiser; prior-region checks.
Run: python3 -I referee_min.py
"""
import math, sys
import mpmath as mp

T4 = [("0.07","69.0","19.6"),("0.09","69","12"),("0.12","68.6","26.2"),("0.17","83","8"),("0.179","75","4"),
      ("0.199","75","5"),("0.20","72.9","29.6"),("0.27","77","14"),("0.28","88.8","36.6"),("0.352","83","14"),
      ("0.3802","83","13.5"),("0.4","95","17"),("0.4004","77","10.2"),("0.4247","87.1","11.2"),
      ("0.44497","92.8","12.9"),("0.4783","80.9","9"),("0.48","97","62"),("0.593","104","13"),("0.68","92","8"),
      ("0.781","105","12"),("0.875","125","17"),("0.88","90","40"),("0.9","117","23"),("1.037","154","20"),
      ("1.3","168","17"),("1.363","160","33.6"),("1.43","177","18"),("1.53","140","14"),("1.75","202","40"),
      ("1.965","186.5","50.4")]
assert len(T4) == 30
D = [(float(z), float(h), float(s)) for z, h, s in T4]
W0 = 1/2.4**2
# y_i = A_i + m*Bm_i + l*Bl_i
COEF = [((1+z)**2, z*(1+z)**2, 1-(1+z)**2, h/(s*s), 1/(s*s)) for z, h, s in D]
GAMMA = W0*73**2 + sum(h*h/(s*s) for z, h, s in D)
SAFETY = 1e-6

def yv(m, l):
    return [A + m*Bm + l*Bl for A, Bm, Bl, wh, w in COEF]

def F(m, l):
    ys = yv(m, l)
    if min(ys) < 0: return math.inf
    al = W0 + sum(w*y for (A, Bm, Bl, wh, w), y in zip(COEF, ys))
    be = W0*73 + sum(wh*math.sqrt(y) for (A, Bm, Bl, wh, w), y in zip(COEF, ys))
    return GAMMA - be*be/al

def imul(a, b):
    p = (a[0]*b[0], a[0]*b[1], a[1]*b[0], a[1]*b[1]); return (min(p), max(p))

def lower(box):
    """Lower bound of F over admissible points of the box, or None if the box has no admissible point."""
    m0, m1, l0, l1 = box
    ylo, yhi = [], []
    for A, Bm, Bl, wh, w in COEF:
        c = [A + m*Bm + l*Bl for m in (m0, m1) for l in (l0, l1)]
        lo, hi = min(c), max(c)
        if hi < 0: return None
        ylo.append(lo); yhi.append(hi)
    alo = W0 + sum(w*max(lo, 0.0) for (A, Bm, Bl, wh, w), lo in zip(COEF, ylo))
    ahi = W0 + sum(w*hi for (A, Bm, Bl, wh, w), hi in zip(COEF, yhi))
    bhi = W0*73 + sum(wh*math.sqrt(hi) for (A, Bm, Bl, wh, w), hi in zip(COEF, yhi))
    blo = W0*73 + sum(wh*math.sqrt(max(lo, 0.0)) for (A, Bm, Bl, wh, w), lo in zip(COEF, ylo))
    nat = GAMMA - bhi*bhi/alo
    if min(ylo) <= 1e-12:
        return nat
    # centred form: F(p) >= F(c) + sum_j min(g_j * d_j) over gradient interval g_j, d_j in [-h_j, h_j]
    mc, lc = (m0+m1)/2, (l0+l1)/2
    Fc = F(mc, lc)
    am = sum(w*Bm for A, Bm, Bl, wh, w in COEF); al_ = sum(w*Bl for A, Bm, Bl, wh, w in COEF)
    bm = (sum(wh*Bm/(2*math.sqrt(hi)) for (A, Bm, Bl, wh, w), hi in zip(COEF, yhi)),
          sum(wh*Bm/(2*math.sqrt(lo)) for (A, Bm, Bl, wh, w), lo in zip(COEF, ylo)))
    bl = (sum(wh*Bl/(2*math.sqrt(lo)) for (A, Bm, Bl, wh, w), lo in zip(COEF, ylo)),
          sum(wh*Bl/(2*math.sqrt(hi)) for (A, Bm, Bl, wh, w), hi in zip(COEF, yhi)))
    B = (blo, bhi); Ainv = (1/ahi, 1/alo)
    t1 = imul(imul(B, Ainv), (-2, -2))          # -2 beta/alpha
    t2 = imul(imul(B, B), imul(Ainv, Ainv))     # beta^2/alpha^2
    gm = tuple(sorted(imul(t1, bm)));  gm = (gm[0] + t2[0]*am if am >= 0 else gm[0] + t2[1]*am,
                                              gm[1] + t2[1]*am if am >= 0 else gm[1] + t2[0]*am)
    gl = tuple(sorted(imul(t1, bl)));  gl = (gl[0] + (t2[0]*al_ if al_ >= 0 else t2[1]*al_),
                                              gl[1] + (t2[1]*al_ if al_ >= 0 else t2[0]*al_))
    hm, hl = (m1-m0)/2, (l1-l0)/2
    cen = Fc - max(abs(gm[0]), abs(gm[1]))*hm - max(abs(gl[0]), abs(gl[1]))*hl
    return max(nat, cen)

def wide_bounds():
    """Bounding box of the wide region: m >= -1/z_i (any i) since l >= 0 and y_i >= 0 force
    1 + m z_i >= l (1 - (1+z_i)^-2) >= 0; l bounded by the LP max l s.t. m <= 1, y_i >= 0 (vertex enumeration)."""
    mlo = max(-1/z for z, h, s in D)
    best = -1
    cons = [(Bm, Bl, -A) for A, Bm, Bl, wh, w in COEF] + [(-1.0, 0.0, -1.0), (0.0, 1.0, 0.0)]  # a m + b l >= c form: Bm m + Bl l >= -A ; -m >= -1 ; l >= 0
    for i in range(len(cons)):
        for j in range(i+1, len(cons)):
            a1, b1, c1 = cons[i]; a2, b2, c2 = cons[j]
            det = a1*b2 - a2*b1
            if abs(det) < 1e-14: continue
            m = (c1*b2 - c2*b1)/det; l = (a1*c2 - a2*c1)/det
            if all(a*m + b*l >= c - 1e-9 for a, b, c in cons): best = max(best, l)
    return mlo, best

def bnb(region, target, keep_below=None, maxboxes=3_000_000, minw=1e-9):
    todo = [region]; nproc = 0; fail = []; low = []; best_up = (math.inf, None)
    while todo:
        b = todo.pop(); nproc += 1
        if nproc > maxboxes: fail.append(b); break
        lb = lower(b)
        if lb is None: continue
        mc, lc = (b[0]+b[1])/2, (b[2]+b[3])/2
        f = F(mc, lc)
        if f < best_up[0]: best_up = (f, (mc, lc))
        if lb - SAFETY >= target: continue
        if b[1]-b[0] < minw and b[3]-b[2] < minw:
            (low if keep_below else fail).append((lb, b)); continue
        m0, m1, l0, l1 = b
        if (m1-m0) >= (l1-l0):
            mm = (m0+m1)/2; todo += [(m0, mm, l0, l1), (mm, m1, l0, l1)]
        else:
            lm = (l0+l1)/2; todo += [(m0, m1, l0, lm), (m0, m1, lm, l1)]
    return nproc, fail, low, best_up

if __name__ == "__main__":
    mlo, lhi = wide_bounds()
    print(f"wide region bounding box: m in [{mlo:.6f}, 1], l in [0, {lhi:.6f}]")
    region = (mlo - 1e-9, 1.0, 0.0, lhi + 1e-9)
    n, fail, low, up = bnb(region, 14.9665)
    print(f"A1: F >= 14.9665 on wide region: boxes={n}, failures={len(fail)}, best centre value={up}")
    # localisation: every admissible point with F < 14.968 lies in the union of the small surviving boxes
    n2, fail2, low2, up2 = bnb(region, 14.968, keep_below=True, minw=2e-3)
    ms = [b[0] for lb, b in low2] + [b[1] for lb, b in low2]
    ls = [b[2] for lb, b in low2] + [b[3] for lb, b in low2]
    print(f"A2: {{F < 14.968}} covered by {len(low2)} boxes in m [{min(ms):.4f},{max(ms):.4f}] l [{min(ls):.4f},{max(ls):.4f}]; fails={len(fail2)}")
    # A3: tight float lower bound just below the minimum
    s0 = SAFETY; SAFETY = 1e-9
    n3, fail3, _, up3 = bnb(region, 14.967037, minw=1e-8)
    SAFETY = s0
    print(f"A3: F >= 14.967037 on wide region (safety 1e-9): boxes={n3}, failures={len(fail3)}")
    # Part B: 50-digit refinement
    mp.mp.dps = 50
    Dm = [(mp.mpf(z), mp.mpf(h), mp.mpf(s)) for z, h, s in T4]
    w0 = 1/mp.mpf("2.4")**2
    def Fm(m, l):
        ys = [m*(1+z)**3 + (1-m-l)*(1+z)**2 + l for z, h, s in Dm]
        al = w0 + sum(y/s**2 for y, (z, h, s) in zip(ys, Dm))
        be = w0*73 + sum(h*mp.sqrt(y)/s**2 for y, (z, h, s) in zip(ys, Dm))
        ga = w0*73**2 + sum(h**2/s**2 for z, h, s in Dm)
        return ga - be**2/al, be/al, min(ys)
    g = lambda m, l: Fm(m, l)[0]
    sol = mp.findroot([lambda m, l: mp.diff(g, (m, l), (1, 0)), lambda m, l: mp.diff(g, (m, l), (0, 1))],
                      (mp.mpf(up[1][0]), mp.mpf(up[1][1])))
    m, l = sol[0], sol[1]
    Fv, H0, ymin = Fm(m, l)
    chi_full = sum((H0*mp.sqrt(m*(1+z)**3 + (1-m-l)*(1+z)**2 + l) - h)**2/s**2 for z, h, s in Dm) + (H0-73)**2*w0
    hess = [[mp.diff(g, (m, l), (2, 0)), mp.diff(g, (m, l), (1, 1))], [mp.diff(g, (m, l), (1, 1)), mp.diff(g, (m, l), (0, 2))]]
    zt = mp.cbrt(2*l/m) - 1
    print("B: minimiser Om =", mp.nstr(m, 15), " OL =", mp.nstr(l, 15), " H0 =", mp.nstr(H0, 15))
    print("   chi2_min (profile) =", mp.nstr(Fv, 20), " full chi2 at (H0,m,l) =", mp.nstr(chi_full, 20))
    print("   Hessian =", [[mp.nstr(x, 6) for x in r] for r in hess], " det =", mp.nstr(hess[0][0]*hess[1][1]-hess[0][1]**2, 6))
    print("   z_t =", mp.nstr(zt, 10), " 2OL/Om =", mp.nstr(2*l/m, 10), " min y_i =", mp.nstr(ymin, 6), " Ok =", mp.nstr(1-m-l, 8))
    print("   prior wedge: 0<=Om<=1:", 0 <= m <= 1, " 1<=2OL/Om<=15.625:", 1 <= 2*l/m <= mp.mpf("15.625"))
    print("   margins: chi2_min - 14.9665 =", mp.nstr(Fv - mp.mpf("14.9665"), 8), "; 14.9675 - chi2_min =", mp.nstr(mp.mpf("14.9675") - Fv, 8))
    for N in (30, 31):
        print(f"   AICc(k=3,N={N}) at min =", mp.nstr(Fv + 6 + mp.mpf(24)/(N-4), 10), f" BIC =", mp.nstr(Fv + 3*mp.log(N), 10),
              " AIC =", mp.nstr(Fv + 6, 10))
