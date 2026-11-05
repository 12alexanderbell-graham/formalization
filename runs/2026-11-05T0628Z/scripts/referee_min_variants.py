"""Referee (run 2026-11-05T0628Z), companion to referee_min.py.
1. Soundness spot-check of the box lower bound (random boxes, random admissible points).
2. Independent dense grid over the wide region (float), and minima on its boundary pieces:
   each E^2(z_i) = 0 line, m = 1, l = 0.
3. Hypothesis attacks: drop m <= 1 and l >= 0 (keep E^2 >= 0); drop everything and use Lean's junk
   sqrt (sqrt of a negative = 0).
4. Readings of Table 5: data-only chi^2 (no prior term), H0 marginalised, typo z = 0.4497, AIC vs AICc.
Run: python3 -I referee_min_variants.py
"""
import math, random, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import referee_min as R

random.seed(1)
# 1. soundness spot-check
worst = math.inf
for _ in range(20000):
    m0 = random.uniform(-0.51, 1); l0 = random.uniform(0, 2.6)
    w = 10**random.uniform(-4, -0.5)
    box = (m0, min(1, m0 + w*random.random()), l0, l0 + w*random.random())
    lb = R.lower(box)
    if lb is None: continue
    for _ in range(20):
        m = random.uniform(box[0], box[1]); l = random.uniform(box[2], box[3])
        f = R.F(m, l)
        if f < math.inf: worst = min(worst, f - lb)
print("1. min over samples of F(p) - lowerbound(box) (must be >= 0):", worst)

# 2. dense grid over the wide region
def grid(mlo, mhi, llo, lhi, n, Ffun=R.F):
    best = (math.inf, None)
    for i in range(n+1):
        m = mlo + (mhi-mlo)*i/n
        for j in range(n+1):
            l = llo + (lhi-llo)*j/n
            f = Ffun(m, l)
            if f < best[0]: best = (f, (m, l))
    return best
print("2. grid 1200^2 wide region:", grid(-0.5089, 1, 0, 2.601, 1200))
# local minima map: coarse grid, list cells that are local minima
n = 300; vals = {}
for i in range(n+1):
    for j in range(n+1):
        vals[i, j] = R.F(-0.5089 + 1.5089*i/n, 2.601*j/n)
locs = []
for (i, j), v in vals.items():
    if v == math.inf: continue
    nb = [vals.get((i+a, j+b), math.inf) for a in (-1, 0, 1) for b in (-1, 0, 1) if (a, b) != (0, 0)]
    if all(v <= x for x in nb): locs.append((v, -0.5089 + 1.5089*i/n, 2.601*j/n))
print("   discrete local minima (300^2 grid incl. boundary):", sorted(locs)[:8])

def golden(f, a, b, it=200):
    g = (math.sqrt(5)-1)/2
    c, d = b - g*(b-a), a + g*(b-a)
    for _ in range(it):
        if f(c) < f(d): b = d
        else: a = c
        c, d = b - g*(b-a), a + g*(b-a)
    x = (a+b)/2; return f(x), x
def minline(f, a, b, n=4000):
    xs = [a + (b-a)*k/n for k in range(n+1)]
    k = min(range(n+1), key=lambda k: f(xs[k]))
    return golden(f, xs[max(k-1, 0)], xs[min(k+1, n)])
# boundary pieces
res = []
for idx, (A, Bm, Bl, wh, w) in enumerate(R.COEF):
    # y_i = 0  ->  l = -(A + m Bm)/Bl  (Bl < 0)
    def fb(m, A=A, Bm=Bm, Bl=Bl):
        l = -(A + m*Bm)/Bl
        if l < 0 or m > 1: return math.inf
        return R.F(m, l - 1e-12)
    v = minline(fb, -0.51, 1)
    if v[0] < math.inf: res.append((v[0], f"y_{idx}=0 (z={R.D[idx][0]})", v[1], -(A + v[1]*Bm)/Bl))
res.append(minline(lambda l: R.F(1.0, l), 0, 2.61) + ("m=1",))
res.append(minline(lambda m: R.F(m, 0.0), -0.51, 1) + ("l=0",))
print("   boundary minima (value, piece, ...), lowest first:")
for r in sorted(res, key=lambda r: r[0])[:6]: print("     ", r)
print("   E^2=0 pieces reachable:", sum(1 for r in res if isinstance(r[1], str) and r[1].startswith('y')),
      " lowest E^2=0 value:", min(r[0] for r in res if isinstance(r[1], str) and r[1].startswith('y')))

# 3a. drop m <= 1, l >= 0 (keep all E^2 >= 0)
print("3a. no m<=1, l>=0 (E^2>=0 only): grids")
for box in [(-3, 3, -3, 3), (-10, 10, -10, 10), (-100, 100, -100, 100), (-1000, 1000, -1000, 1000)]:
    print("    ", box, grid(*box, 800))
# 3b. Lean junk: sqrt(negative) = 0, no hypothesis at all
def Fjunk(m, l):
    ys = [max(y, 0.0) for y in R.yv(m, l)]
    al = R.W0 + sum(w*y for (A, Bm, Bl, wh, w), y in zip(R.COEF, ys))
    be = R.W0*73 + sum(wh*math.sqrt(y) for (A, Bm, Bl, wh, w), y in zip(R.COEF, ys))
    return R.GAMMA - be*be/al
print("3b. Lean junk sqrt, no hypotheses: grids")
for box in [(-3, 3, -3, 3), (-20, 20, -20, 20), (-200, 200, -200, 200)]:
    print("    ", box, grid(*box, 800, Fjunk))

# 4. readings
def Fdata(m, l):  # H0 free, no prior term at all
    ys = R.yv(m, l)
    if min(ys) < 0: return math.inf
    al = sum(w*y for (A, Bm, Bl, wh, w), y in zip(R.COEF, ys))
    be = sum(wh*math.sqrt(y) for (A, Bm, Bl, wh, w), y in zip(R.COEF, ys))
    return (R.GAMMA - R.W0*73**2) - be*be/al
def refine(f, m, l, st=0.01):
    v = f(m, l)
    while st > 1e-10:
        imp = False
        for dm, dl in [(st, 0), (-st, 0), (0, st), (0, -st), (st, st), (-st, -st), (st, -st), (-st, st)]:
            u = f(m+dm, l+dl)
            if u < v: m, l, v, imp = m+dm, l+dl, u, True
        if not imp: st /= 2
    return v, m, l
g = grid(-0.5089, 1, 0, 2.601, 600, Fdata); print("4a. data-only chi2 (no H0 prior), wide region:", refine(Fdata, *g[1]))
def inprior(m, l): return 0 <= m <= 1 and m <= 2*l <= 15.625*m
Fdp = lambda m, l: Fdata(m, l) if inprior(m, l) else math.inf
g = grid(0, 1, 0, 7.8125, 800, Fdp); print("    data-only chi2, prior region:", refine(Fdp, *g[1]))
def Fmarg(m, l):  # -2 ln of the prior-averaged likelihood over H0 (normalised Gaussian prior), chi2 form
    ys = R.yv(m, l)
    if min(ys) < 0: return math.inf
    al = R.W0 + sum(w*y for (A, Bm, Bl, wh, w), y in zip(R.COEF, ys))
    return R.F(m, l) + math.log(al*2.4**2)
g = grid(-0.5089, 1, 0, 2.601, 400, Fmarg); print("4b. H0 marginalised:", refine(Fmarg, *g[1]))
# typo-corrected z
save = R.COEF[14]
z, h, s = 0.4497, 92.8, 12.9
R.COEF[14] = ((1+z)**2, z*(1+z)**2, 1-(1+z)**2, h/(s*s), 1/(s*s))
print("4c. z15 = 0.4497:", refine(R.F, 0.436, 0.981))
R.COEF[14] = save
c = 14.967038174884521725
print("4d. c needed for printed 21.41 under AICc(k=3,N): ", {N: round(21.41 - 6 - 24/(N-4), 4) for N in (30, 31)},
      " under AIC: ", round(21.41 - 6, 4))
print("    N at which chi2_min + 6 + 24/(N-4) = 21.41:", 4 + 24/(21.41 - 6 - c))
for k in (1, 2, 3, 4, 5):
    print(f"    k={k}: AICc at chi2_min, N=31: {c + 2*k + 2*k*(k+1)/(31-k-1):.4f}; N=30: {c + 2*k + 2*k*(k+1)/(30-k-1):.4f}; AIC: {c+2*k:.4f}")
