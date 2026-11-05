"""(float64 only; mpmath unavailable here) Margins for a frozen statement on Moresco+2016 Table 4 / Table 5 oLCDM row (profiled H0, Gaussian prior 73+-2.4).
F(Om,OL) = gamma - beta^2/alpha  (= min over H0 of chi2 + (H0-73)^2/2.4^2), E^2 = (1+z)^2 (1 + Om z - OL) + OL.
Run: python3 -I screen_moresco16_margins.py   (imports the table from screen_moresco16.py by path)."""
import importlib.util, sys, numpy as np
from math import sqrt as msqrt, log as mlog
mpf = float
spec = importlib.util.spec_from_file_location('m16', __file__.replace('_margins', ''))
m16 = importlib.util.module_from_spec(spec); sys.argv = ['x']; spec.loader.exec_module(m16)
T = [(float(a), float(b), float(c)) for a, b, c in m16.T4]
Hb, sH = mpf(73), mpf('2.4')

def F(Om, OL):
    al = 1 / sH**2; be = Hb / sH**2; ga = Hb**2 / sH**2
    for z, H, s in T:
        E2 = (1 + z)**2 * (1 + Om * z - OL) + OL
        if E2 <= 0: return float('inf')
        w = 1 / s**2; al += E2 * w; be += msqrt(E2) * H * w; ga += H**2 * w
    return ga - be**2 / al

# Newton on grad F (numerical derivatives in mpmath)
x = [mpf('0.43617314'), mpf('0.98143852')]
for _ in range(8):
    h = 1e-5
    def g(i, p):
        q1 = list(p); q2 = list(p); q1[i] += h; q2[i] -= h; return (F(*q1) - F(*q2)) / (2 * h)
    G = [g(0, x), g(1, x)]
    Hm = [[(g(i, [x[0] + (h if j == 0 else 0), x[1] + (h if j == 1 else 0)]) - g(i, [x[0] - (h if j == 0 else 0), x[1] - (h if j == 1 else 0)])) / (2 * h) for j in range(2)] for i in range(2)]
    d = Hm[0][0] * Hm[1][1] - Hm[0][1] * Hm[1][0]
    dx = [(Hm[1][1] * G[0] - Hm[0][1] * G[1]) / d, (-Hm[1][0] * G[0] + Hm[0][0] * G[1]) / d]
    x = [x[0] - dx[0], x[1] - dx[1]]
Fs = F(*x); zt = (2 * x[1] / x[0])**(mpf(1) / 3) - 1
print('argmin Om =', f'{x[0]:.10f}', ' OL =', f'{x[1]:.10f}', ' Fmin =', f'{Fs:.10f}', ' zt =', f'{zt:.8f}')
print('Hessian', [[round(v,3) for v in r] for r in Hm])
# H0 at the minimum
al = 1 / sH**2 + sum(((1 + z)**2 * (1 + x[0] * z - x[1]) + x[1]) / s**2 for z, H, s in T)
be = Hb / sH**2 + sum(msqrt((1 + z)**2 * (1 + x[0] * z - x[1]) + x[1]) * H / s**2 for z, H, s in T)
print('H0* =', be / al)
# implied chi2 by printed AICc / BIC, k=3, N=30/31
for N in (30, 31):
    k = 3
    print(f'N={N}: chi2 implied by AICc 21.41: {21.41 - 2*k - 2*k*(k+1)/(N-k-1):.4f}; by BIC 25.71: {25.71 - k*mlog(N):.4f};'
          f' AICc,BIC from Fmin: {float(Fs) + 2*k + 2*k*(k+1)/(N-k-1):.4f}, {float(Fs) + k*mlog(N):.4f}')
# coarse float scan of the paper's prior region Om in [0,1], zt in [0,1.5] (excluding E^2<=0)
Ff = lambda a, b: float(F(mpf(a), mpf(b)))
z = np.array([r[0] for r in m16.T4]); Hd = np.array([r[1] for r in m16.T4], float); sd = np.array([r[2] for r in m16.T4], float)
def Fn(Om, OL):
    E2 = (1 + z)**2 * (1 + Om * z - OL) + OL
    if np.any(E2 <= 0): return np.inf
    w = 1 / sd**2; al = 1 / 2.4**2 + np.sum(E2 * w); be = 73 / 2.4**2 + np.sum(np.sqrt(E2) * Hd * w); ga = 73**2 / 2.4**2 + np.sum(Hd**2 * w)
    return ga - be**2 / al
oms = np.linspace(0, 1, 801); zts = np.linspace(0, 1.5, 601)
V = np.array([[Fn(om, om * (1 + t)**3 / 2) for om in oms] for t in zts])
fin = np.isfinite(V); print('prior-region scan min', V[fin].min(), ' fraction E2<=0 cells', 1 - fin.mean())
for d in (0.01, 0.05, 0.1):
    ii = np.argwhere(V <= float(Fs) + d)
    print(f'  set F<=Fmin+{d}: Om in [{oms[ii[:,1]].min():.4f},{oms[ii[:,1]].max():.4f}], zt in [{zts[ii[:,0]].min():.4f},{zts[ii[:,0]].max():.4f}]')
# box [0,1]x[0,1.2] in (Om,OL) and complement in the wedge
ob = np.linspace(0, 1, 401); lb = np.linspace(0, 2.0, 801)
W = np.array([[Fn(a, b) for a in ob] for b in lb]); fw = np.isfinite(W)
print('box Om[0,1] x OL[0,2] min', W[fw].min(), ' min over OL>=1.3:', W[(lb[:, None] >= 1.3) & fw].min() if True else '')
print('edges of box: Om=0', np.nanmin(np.where(fw[:,0], W[:,0], np.inf)), ' Om=1', np.nanmin(np.where(fw[:,-1], W[:,-1], np.inf)), ' OL=0', W[0][fw[0]].min())
