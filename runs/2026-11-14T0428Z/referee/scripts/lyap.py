"""Minimum of u v^3 on {V <= V150}, V = (u-1-log u) + (v-2-2 log(v/2)).
uv^3 has no interior critical point (grad log(uv^3) = (1/u, 3/v) != 0), so the min is on the boundary.
Lagrange: (1/u, 3/v) = lam * (1 - 1/u, 1 - 2/v)  =>  1/(u-1) = 3/(v-2) * ... solve numerically by
parametrizing the boundary with an angle and minimizing, with mpmath at 30 digits; checked by Lagrange root."""
import mpmath as mp
mp.mp.dps = 30
V150 = mp.mpf('0.0060764306018455')  # from be_min.py method A (15 digits)
m2 = mp.mpf('0.694366521128555379')
def V(u, v): return (u - 1 - mp.log(u)) + (v - 2 - 2 * mp.log(v / 2))
def boundary_point(th):
    # ray from (1,2) in direction (cos th, sin th); V is convex, so unique crossing
    d = (mp.cos(th), mp.sin(th))
    r = mp.findroot(lambda r: V(1 + r * d[0], 2 + r * d[1]) - V150, mp.mpf('0.1'))
    return 1 + r * d[0], 2 + r * d[1]
def f(th):
    u, v = boundary_point(th); return u * v ** 3
# coarse scan
best = min((f(2 * mp.pi * k / 720), k) for k in range(720))
th0 = 2 * mp.pi * best[1] / 720
# refine by golden-section/derivative root
thm = mp.findroot(lambda th: mp.diff(f, th), th0)
u, v = boundary_point(thm)
print('min u v^3 on sublevel set =', mp.nstr(u * v ** 3, 15), ' at u,v =', mp.nstr(u, 12), mp.nstr(v, 12))
print('4 pi m(xi2)^2 =', mp.nstr(4 * mp.pi * m2 ** 2, 15))
print('implied lower bound for m beyond 150: sqrt(min/(4pi)) =', mp.nstr(mp.sqrt(u * v ** 3 / (4 * mp.pi)), 12))
# Lagrange check: grad(log uv^3) parallel to grad V
print('Lagrange residual:', mp.nstr((1 / u) * (1 - 2 / v) - (3 / v) * (1 - 1 / u), 5))
