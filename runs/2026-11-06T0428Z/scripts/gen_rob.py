"""Robertson network: rational polynomial cells + certified (exact rational) defect and
one-sided bounds for Work.Sim.OneSided.onesided_cell / rob_onesided.
Reduced system in (y2, y3), y1 = 1 - y2 - y3; weighted norm w*e2^2 + e3^2, w = D^2.
Usage: python3 gen_rob.py [deg] [out.json]"""
import sys, json, math
from fractions import Fraction as Fr
import numpy as np
from scipy.integrate import solve_ivp

K1, K2, K3 = Fr(1, 25), Fr(10000), Fr(30000000)
k1, k2, k3 = 0.04, 1e4, 3e7
D = Fr(70); W = D * D
DEG = int(sys.argv[1]) if len(sys.argv) > 1 else 10
OUT = sys.argv[2] if len(sys.argv) > 2 else None
TEND = Fr(40)

def F(t, y):
    y2, y3 = y; y1 = 1 - y2 - y3
    return [k1*y1 - k2*y2*y3 - k3*y2*y2, k3*y2*y2]
def Jac(t, y):
    y2, y3 = y
    return [[-k1 - k2*y3 - 2*k3*y2, -k1 - k2*y2], [2*k3*y2, 0.0]]
ref = solve_ivp(F, (0, 40), [0.0, 0.0], method='Radau', jac=Jac, rtol=1e-13, atol=1e-22,
                dense_output=True)
assert ref.success

# cell grid: geometric from h0, capped
def grid():
    ts = [Fr(0)]; h = Fr(1, 100000)
    while ts[-1] < TEND:
        t = ts[-1] + h
        if t > TEND: t = TEND
        ts.append(t)
        h = min(h * Fr(3, 2), Fr(2))
        # round h to 2 significant decimal digits
        e = math.floor(math.log10(float(h)))
        h = Fr(round(float(h) / 10**e * 10), 10) * Fr(10)**e
    return ts

# polynomial helpers (lists of Fractions, low order first)
def padd(a, b):
    n = max(len(a), len(b)); return [(a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0) for i in range(n)]
def pscale(a, c): return [c*x for x in a]
def pmul(a, b):
    r = [Fr(0)]*(len(a)+len(b)-1)
    for i, x in enumerate(a):
        if x == 0: continue
        for j, y in enumerate(b): r[i+j] += x*y
    return r
def pder(a): return [i*a[i] for i in range(1, len(a))] or [Fr(0)]
def peval(a, x):
    r = Fr(0)
    for c in reversed(a): r = r*x + c
    return r
def absbound(a, h):  # sum |c_k| h^k
    return sum(abs(c) * h**k for k, c in enumerate(a))
def lowup(a, h):
    rest = sum(abs(c) * h**k for k, c in enumerate(a) if k > 0)
    return a[0] - rest, a[0] + rest

def fit(t0, h, c0, deg):
    """Collocation polynomial p(u), u = t - (t0 + h/2) in [-h/2, h/2], degree deg, with
    p(-h/2) = c0 and the ODE at deg Chebyshev points; Newton in float64 from a least-squares fit
    of the reference. Coefficients rounded to rationals (y2: 1e-26, y3: 1e-22 relative to (h/2)^k)."""
    n = deg
    hf = float(h); r = hf / 2; c0f = [float(c0[0]), float(c0[1])]
    sj = -np.cos(np.pi * (np.arange(n) + 0.5) / n)                  # points in [-1,1]
    m = 3 * n
    sl = -np.cos(np.pi * (np.arange(m) + 0.5) / m)
    Y = ref.sol(float(t0) + r + sl * r)
    V = np.vstack([(sl)**k for k in range(0, n + 1)]).T
    a = np.concatenate([np.linalg.lstsq(V, Y[c], rcond=None)[0] for c in range(2)])
    N = n + 1
    P = np.vstack([sj**k for k in range(0, N)]).T                     # n x N
    dP = np.vstack([k * sj**(k - 1) if k > 0 else 0 * sj for k in range(0, N)]).T / r
    e0 = np.array([(-1.0)**k for k in range(N)])                      # value at u = -h/2
    for it in range(40):
        a2, a3 = a[:N], a[N:]
        y2 = P @ a2; y3 = P @ a3
        r2 = dP @ a2 - (k1*(1 - y2 - y3) - k2*y2*y3 - k3*y2*y2)
        r3 = dP @ a3 - k3*y2*y2
        res = np.concatenate([[e0 @ a2 - c0f[0]], r2, [e0 @ a3 - c0f[1]], r3])
        Z = np.zeros(N)
        J11 = dP - (-k1 - k2*y3 - 2*k3*y2)[:, None] * P
        J12 = -(-k1 - k2*y2)[:, None] * P
        J21 = -(2*k3*y2)[:, None] * P
        J22 = dP
        Jm = np.block([[e0[None, :], Z[None, :]], [J11, J12], [Z[None, :], e0[None, :]], [J21, J22]])
        da = np.linalg.solve(Jm, -res)
        a = a + da
        if np.max(np.abs(da)) < 1e-300: break
    out = []
    for comp in range(2):
        coef = a[comp*N:(comp+1)*N]
        scale = Fr(10)**(26 if comp == 0 else 22)
        out.append([Fr(round(c * float(scale))) / scale / Fr(r).limit_denominator(10**30)**0 / (h/2)**k
                    for k, c in enumerate(coef)])
    return out

def shift(a, c):
    from math import comb
    n = len(a); r = [Fr(0)]*n
    for i, ai in enumerate(a):
        for j in range(i+1): r[j] += ai*comb(i, j)*c**(i-j)
    return r

def roundc(x, digits):
    s = Fr(10)**digits
    return Fr(round(x * s)) / s

def mu_for(A, Cm, B):
    K0 = ((W*K2 + K3) + W*K3/D) * B
    a = W*A - K0
    # smallest mu with Cm^2 <= 4 mu (a + W mu): mu = (-a + sqrt(a^2 + W Cm^2)) / (2W)
    mu = (-float(a) + math.sqrt(float(a)**2 + float(W*Cm*Cm))) / (2*float(W))
    mu = max(mu, 1e-12) * 1.01 + 1e-12
    m = Fr(mu).limit_denominator(10**8)
    while not (Cm*Cm <= 4*m*(a + W*m)): m *= Fr(11, 10)
    return m

def run(deg):
    ts = grid()
    c = [Fr(0), Fr(0)]
    delta = Fr(1, 10**30)
    cells = []
    for i in range(len(ts) - 1):
        t0, t1 = ts[i], ts[i+1]; h = t1 - t0
        p2, p3 = fit(t0, h, c, deg)
        # defects
        f2 = padd(padd(pscale(padd([Fr(1)], pscale(padd(p2, p3), -1)), K1), pscale(pmul(p2, p3), -K2)), pscale(pmul(p2, p2), -K3))
        f3 = pscale(pmul(p2, p2), K3)
        d2 = padd(pder(p2), pscale(f2, -1)); d3 = padd(pder(p3), pscale(f3, -1))
        R = h/2
        e2 = absbound(d2, R); e3 = absbound(d3, R)
        eps2 = W*e2*e2 + e3*e3
        eps = Fr(math.sqrt(float(eps2)) * 1.001 + 1e-40).limit_denominator(10**40)
        while not (eps*eps > eps2): eps *= Fr(1001, 1000)
        L2, U2 = lowup(p2, R); L3, U3 = lowup(p3, R)
        A = K1 + K2*L3 + 2*K3*L2
        Cfun = lambda x2: -(W*K1) - W*K2*x2 + 2*K3*x2
        Cm = max(abs(Cfun(L2)), abs(Cfun(U2)))
        # B guess then mu, iterate
        st2, st3 = peval(p2, -R), peval(p3, -R)
        dstart = delta + D*abs(c[0] - st2) + abs(c[1] - st3)
        dstart = roundc(dstart, 40) + Fr(1, 10**40)
        B = (dstart + eps*h) * 2
        for _ in range(5):
            mu = mu_for(A, Cm, B)
            x = mu*h
            assert x <= 1, (float(t0), float(mu))
            Bn = (dstart + eps*h) * (1 + x + x*x)
            if Bn <= B: break
            B = Bn * Fr(11, 10)
        B = roundc(Bn, 40) + Fr(1, 10**40)
        # end value and rounding into next centre
        end2, end3 = peval(p2, R), peval(p3, R)
        n2, n3 = roundc(end2, 24), roundc(end3, 20)
        m2, m3 = abs(end2 - n2), abs(end3 - n3)
        dnext = B + D*m2 + m3
        dnext = roundc(dnext, 40) + Fr(1, 10**40)
        cells.append(dict(t0=t0, h=h, p2=p2, p3=p3, d2=d2, d3=d3, e2=e2, e3=e3, eps=eps, mu=mu,
                          A=A, Cm=Cm, L2=L2, U2=U2, L3=L3, delta=delta, dstart=dstart, c2=c[0], c3=c[1], B=B, n2=n2, n3=n3,
                          dnext=dnext))
        delta = dnext; c = [n2, n3]
    return cells

if __name__ == '__main__':
    cells = run(DEG)
    tot = 0
    for i, cl in enumerate(cells):
        print(f"{i:3d} t0={float(cl['t0']):.6g} h={float(cl['h']):.3g} eps={float(cl['eps']):.2e} "
              f"mu={float(cl['mu']):.3g} B={float(cl['B']):.3e} y2={float(cl['n2']):.6e}")
    last = cells[-1]
    print('cells', len(cells), 'final delta', float(last['dnext']),
          ' y2 err <=', float(last['dnext']/D), ' y3 err <=', float(last['dnext']))
    print('y2(40) ~', float(last['n2']), ' y3(40) ~', float(last['n3']), ' y1 ~', float(1-last['n2']-last['n3']))
    if OUT:
        json.dump([{k: str(v) if not isinstance(v, list) else [str(x) for x in v] for k, v in cl.items()} for cl in cells], open(OUT, 'w'))
