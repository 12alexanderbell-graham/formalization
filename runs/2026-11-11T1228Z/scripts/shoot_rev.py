# Run 2026-11-11T1228Z: float shooting (mpmath taylor ODE) for the scaled adverse-sign Falkner–Skan
# g''' = -K g g'' + 1 - g'^2, g(0)=g'(0)=0, g''(0)=A, K = 2500/497; classifies A as over (p>1) or
# slow (p falls back below ... / q<0 late) to locate both decay branches.
import mpmath as mp, sys
mp.mp.dps = 30
K = mp.mpf(2500)/497
def run(A, L=12):
    f = lambda t, y: [y[1], y[2], -K*y[0]*y[2] + 1 - y[1]**2]
    sol = mp.odefun(f, 0, [0, 0, A])
    t = mp.mpf(0); h = mp.mpf('0.05')
    while t < L:
        t += h; y = sol(t)
        if y[1] > 1: return 'over', float(t)
        if y[2] < 0 and y[1] > 0.3: return 'under', float(t)
    return 'none', float(t)
def bisect(a, b, n=40):
    ra = run(a)[0]
    for _ in range(n):
        m = (a+b)/2; r = run(m)[0]
        if r == ra: a = m
        else: b = m
        print(mp.nstr(a, 15), mp.nstr(b, 15), ra, flush=True)
    return a, b
if __name__ == '__main__':
    for A in [-0.013, -0.012, -0.0116, -0.0115, -0.011, 0, 0.0117, 0.012]:
        print(A, run(mp.mpf(A)), flush=True)
