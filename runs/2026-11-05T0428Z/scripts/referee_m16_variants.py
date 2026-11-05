"""Referee variant search for Moresco+2016 Table 5: is there ANY natural reading under which a row of
Table 5 is internally consistent (both printed numbers from one -2 ln L_max), and under which the
printed numbers match the fit to Table 4?  Run: python3 -I referee_m16_variants.py"""
import math, itertools, importlib.util, sys
import mpmath as mp
spec = importlib.util.spec_from_file_location('r', __file__.replace('_variants', ''))
R = importlib.util.module_from_spec(spec); spec.loader.exec_module(R)
mp.mp.dps = 30
PR = {'oLCDM': (3, 21.41, 25.71), 'piecewise': (4, 23.99, 28.72), 'line': (2, 32.42, 35.29)}
TOL = 0.005

# ---- A. data-independent: which (formula, kA, NA, kB, NB) make AICc_col - BIC_col match? ----
def colA(form, k, N):
    if form == 'AICc(5.4)': return 2*k + 2*k*(k+1)/(N-k-1)
    if form == 'AIC':       return 2*k
    if form == 'AICc,N-k':  return 2*k + 2*k*(k+1)/(N-k)
    if form == 'AICc,N-k+1': return 2*k + 2*k*(k+1)/(N-k+1)
def colB(form, k, N):
    if form == 'k lnN':    return k*math.log(N)
    if form == 'k log10N': return k*math.log10(N)
    if form == 'k ln(N/2pi)': return k*math.log(N/(2*math.pi))
print('A. Data-independent consistency (needs |pen_A - pen_B - (AICc-BIC)_printed| <= 0.01):')
for row, (k0, A, B) in PR.items():
    d = A - B
    hits = []
    for fa, fb in itertools.product(['AICc(5.4)', 'AIC', 'AICc,N-k', 'AICc,N-k+1'], ['k lnN', 'k log10N', 'k ln(N/2pi)']):
        for kA, kB in itertools.product(range(1, 7), repeat=2):
            for NA, NB in itertools.product(range(28, 33), repeat=2):
                if NA - kA - 1 <= 0: continue
                if abs(colA(fa, kA, NA) - colB(fb, kB, NB) - d) <= 2*TOL:
                    hits.append((fa, kA, NA, fb, kB, NB))
    same = [h for h in hits if h[1] == h[4] and h[2] == h[5]]
    print(f'  {row:9s} printed diff {d:+.2f}: {len(hits)} hits with N in 28..32, k in 1..6;'
          f' with one k and one N: {same}')
    nat = [h for h in hits if h[1] == k0 and h[4] == k0 and h[2] in (30, 31) and h[5] in (30, 31)]
    print(f'             with the paper\'s k={k0} and N_A,N_B in {{30,31}}: {nat}')
    wide = [(kk, N) for kk in range(1, 7) for N in range(kk+2, 200)
            if abs(2*kk + 2*kk*(kk+1)/(N-kk-1) - kk*math.log(N) - d) <= 2*TOL]
    print(f'             Eq.5.4 with any one (k, N<200): {wide}')

# ---- B. our chi2_min under each reading ----
rows = R.table()
Om, OL, H0, Fo = R.olcdm_min(rows); Fo = float(Fo)
_, _, cl, _ = R.line_fit(rows); cl = float(cl)
cp, _ = R.piecewise(rows, [i/4000 for i in range(1, 8001)])
chi = {'oLCDM': Fo, 'piecewise': cp, 'line': cl}
print('\nB. Implied -2lnLmax from each printed number vs our chi2_min')
for row, (k, A, B) in PR.items():
    for N in (30, 31):
        print(f'  {row:9s} N={N}: from AICc(5.4) {A-2*k-2*k*(k+1)/(N-k-1):.4f}, from AIC-reading {A-2*k:.4f},'
              f' from BIC {B-k*math.log(N):.4f};  our chi2_min {chi[row]:.4f}')
print('  Reading "AICc column is plain AIC, N=31": offsets printed - ours:')
lo, hi = -1e9, 1e9
for row in ('oLCDM', 'line'):
    k, A, B = PR[row]
    oa = A - (chi[row] + 2*k); ob = B - (chi[row] + k*math.log(31))
    print(f'    {row}: AIC col {oa:+.4f}, BIC col {ob:+.4f}')
    for o in (oa, ob): lo = max(lo, o - TOL); hi = min(hi, o + TOL)
print(f'    common constant delta reproducing all four numbers to +-0.005: [{lo:.4f}, {hi:.4f}]' if lo <= hi else '    none')
k, A, B = PR['piecewise']
print(f'    piecewise under same reading: AIC col -> c={A-8:.3f}, BIC col -> c={B-4*math.log(31):.3f} (inconsistent)')

# ---- C. H0-prior / likelihood variants for the oLCDM and line chi2 ----
print('\nC. Variants of the statistic (chi2_min oLCDM, line); printed-implied under AICc(5.4) N=31: 14.52/15.41 and 27.99/28.42')
def oL(H0p, sp, rows=rows):
    return float(R.olcdm_min(rows, H0p=mp.mpf(H0p), sp=mp.mpf(sp))[3])
def ln(H0p, sp, with_H0=True, rows=rows):
    from fractions import Fraction as Fr
    pts = [(Fr(0), Fr(H0p), Fr(sp))] if with_H0 else []
    for z, H, s in rows:
        z, H, s = Fr(z), Fr(H), Fr(s); pts.append((z, H/(1+z), s/(1+z)))
    S=Sx=Sxx=Sy=Sxy=Syy=Fr(0)
    for x, y, s in pts:
        w = 1/s**2; S+=w; Sx+=w*x; Sxx+=w*x*x; Sy+=w*y; Sxy+=w*x*y; Syy+=w*y*y
    D = S*Sxx - Sx**2; a = (Sxx*Sy - Sx*Sxy)/D; b = (S*Sxy - Sx*Sy)/D
    return float(Syy - a*Sy - b*Sxy)
for H0p, sp in (('73', '2.4'), ('73.8', '2.4'), ('73.24', '1.74'), ('73.02', '1.79'), ('72', '3'), ('74.3', '2.1')):
    print(f'  H0 prior {H0p}+-{sp}: oLCDM {oL(H0p, sp):.4f}, line {ln(H0p, sp):.4f}')
print(f'  typo 0.44497->0.4497: oLCDM {float(R.olcdm_min(R.table(True))[3]):.4f}, line {ln("73","2.4",rows=R.table(True)):.4f}')
# H0 fixed at 73 (no profile) in oLCDM
f73 = lambda a, b: R.chi2_full(mp.mpf(73), a, b, rows)
s = mp.findroot([lambda a, b: mp.diff(f73, (a, b), (1, 0)), lambda a, b: mp.diff(f73, (a, b), (0, 1))], (mp.mpf('0.43'), mp.mpf('0.98')))
print(f'  oLCDM with H0 fixed at 73: chi2_min {float(f73(s[0], s[1])):.4f}')
# H0 prior counted twice in oLCDM (prior + a z=0 data point)
f2 = lambda a, b: R.Fprof(a, b, rows, sp=mp.mpf('2.4')/mp.sqrt(2))
s2 = mp.findroot([lambda a, b: mp.diff(f2, (a, b), (1, 0)), lambda a, b: mp.diff(f2, (a, b), (0, 1))], (mp.mpf('0.43'), mp.mpf('0.98')))
print(f'  oLCDM with H0 = 73+-2.4 counted twice: chi2_min {float(f2(s2[0], s2[1])):.4f}')
# analytic marginalisation over H0 (Gaussian prior, unnormalised flat in H0 otherwise): -2lnL = F + ln(alpha*sp^2)
al, be, ga = R.abg(Om, OL, rows)
print(f'  oLCDM marginal over H0 at best fit: F + ln(alpha*2.4^2) = {Fo + float(mp.log(al*mp.mpf("2.4")**2)):.4f}')
# Gaussian normalisation constants
cn_o = sum(math.log(2*math.pi*float(s)**2) for _, _, s in rows) + math.log(2*math.pi*2.4**2)
cn_l = sum(math.log(2*math.pi*(float(s)/(1+float(z)))**2) for z, _, s in rows) + math.log(2*math.pi*2.4**2)
print(f'  Gaussian normalisation sum ln(2 pi sigma^2): oLCDM {cn_o:.2f}, line {cn_l:.2f} (would add these to -2lnL)')

# ---- D. Bayesian marginal likelihood over the uniform prior box (Om in [0,1], z_t in [0,1.5]) ----
import numpy as np
T = [(float(z), float(H), float(s)) for z, H, s in rows]
def Ff(Om, zt):
    OLv = Om*(1+zt)**3/2; al = 1/5.76; be = 73/5.76; ga = 73**2/5.76
    for z, H, s in T:
        E2 = Om*(1+z)**3 + (1-Om-OLv)*(1+z)**2 + OLv
        if E2 <= 0: return None
        w = 1/s**2; al += E2*w; be += math.sqrt(E2)*H*w; ga += H*H*w
    return ga - be*be/al, al
n1, n2 = 400, 300; acc = 0.0; accw = 0.0; momz = 0.0; momO = 0.0
for i in range(n1):
    Omv = (i+0.5)/n1
    for j in range(n2):
        ztv = 1.5*(j+0.5)/n2
        r = Ff(Omv, ztv)
        if r is None: continue
        L = math.exp(-(r[0]-Fo)/2)
        acc += L; momz += L*ztv; momO += L*Omv
cell = (1/n1)*(1.5/n2); vol = 1.5
ev = acc*cell/vol
print(f'\nD. -2 ln (prior-averaged profile likelihood over (Om,z_t) box) = {Fo - 2*math.log(ev):.4f}'
      f'  (chi2_min {Fo:.4f}); posterior means Om={momO/acc:.4f}, z_t={momz/acc:.4f}')
zbar, Obar = momz/acc, momO/acc
r = Ff(Obar, zbar)
print(f'   chi2 at posterior-mean (Om, z_t): {r[0]:.4f}  (offset {r[0]-Fo:+.4f})')

# ---- E. claim-1 margins over every real N in (k+1, 31]: h(N) = 2k + 2k(k+1)/(N-k-1) - k ln N is strictly
#      decreasing (h' = -2k(k+1)/(N-k-1)^2 - k/N < 0), so min over the range is h(31); need h(31) - d > 0.01 ----
print('\nE. Claim 1: h(31) - printed(AICc-BIC); the theorem needs > 0.01 (dense check over N too)')
for row, (k, A, B) in PR.items():
    d = A - B
    h = lambda N: 2*k + 2*k*(k+1)/(N-k-1) - k*math.log(N)
    dense = min(h(k+1 + (31-k-1)*t/200000) for t in range(1, 200001))
    print(f'  {row:9s} k={k}: h(31)={h(31):+.5f}, printed {d:+.2f}, margin {h(31)-d-0.01:.4f}; dense min h = {dense:+.5f}')

# ---- F. Any (penalty formula, k_A, N_A, k_B, N_B) with c = OUR chi2_min reproducing BOTH printed numbers? ----
print('\nF. Readings with c = our chi2_min reproducing both printed numbers of a row (k 1..6, N 2..100):')
for row, (k0, A, B) in PR.items():
    c = chi[row]; ha = []; hb = []
    for fa in ('AICc(5.4)', 'AIC', 'AICc,N-k', 'AICc,N-k+1'):
        for kA in range(1, 7):
            for NA in range(kA+2, 101):
                if abs(c + colA(fa, kA, NA) - A) <= TOL: ha.append((fa, kA, NA))
    for fb in ('k lnN', 'k log10N', 'k ln(N/2pi)'):
        for kB in range(1, 7):
            for NB in range(2, 101):
                if abs(c + colB(fb, kB, NB) - B) <= TOL: hb.append((fb, kB, NB))
    print(f'  {row:9s}: AICc col matches {ha[:8]}{"..." if len(ha) > 8 else ""}; BIC col matches {hb}')
