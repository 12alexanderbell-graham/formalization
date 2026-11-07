# Float study (run 2026-11-07T1228Z): Blasius f''' + f f''/2 = 0, f(0)=f'(0)=0, f'(inf)=1.
# Scaling: g''' + g g''/2 = 0, g(0)=g'(0)=0, g''(0)=1; alpha = g'(inf); sigma = f''(0) = alpha^(-3/2).
import mpmath as mp
mp.mp.dps = 40
def F(t, y): return [y[1], y[2], -y[0]*y[2]/2]
for L in [6, 8, 10, 12]:
    sol = mp.odefun(F, 0, [mp.mpf(0), mp.mpf(0), mp.mpf(1)])
    g, p, q = sol(L)
    tail = 2*q/g   # bound int_L^inf g'' <= 2 g''(L)/g(L)
    lo, hi = p, p + tail
    print(L, mp.nstr(g, 12), mp.nstr(p, 20), mp.nstr(q, 5), 'tail', mp.nstr(tail, 5),
          'sigma in', mp.nstr(hi**-1.5, 20), mp.nstr(lo**-1.5, 20))
