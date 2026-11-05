"""Referee route B: dimensional PR, critical point from numerical derivatives (no Omega constants),
Maxwell state from root finding + quadrature, uniqueness scan of the equal-area function."""
from mpmath import mp, mpf, sqrt, diff, findroot, quad, log10, polyroots, re, im
mp.dps = 40
R = mpf('8.314462618'); ac = mpf('0.6'); b = mpf('4.5e-5')   # arbitrary positive data
u, w = 2, -1
def P(a, T, v): return R*T/(v - b) - a/(v**2 + u*b*v + w*b**2)
# critical point of the a = ac family
F = lambda T, v: [diff(lambda x: P(ac, T, x), v, 1), diff(lambda x: P(ac, T, x), v, 2)]
Tc, vc = findroot(F, (mpf(300), mpf(4)*b))
Pc = P(ac, Tc, vc)
print("Tc", Tc, "vc/b", vc/b, "Zc", Pc*vc/(R*Tc), "Omega_b", b*Pc/(R*Tc), "Omega_a", ac*Pc/(R*Tc)**2)
kap = mpf('0.37464') + mpf('1.54226') - mpf('0.26992')
a7 = ac*(1 + kap*(1 - sqrt(mpf(7)/10)))**2
T7 = mpf(7)/10*Tc
p = lambda v: P(a7, T7, v)
# spinodals on (b, inf)
dp = lambda v: diff(p, v)
# numerator of dp: -RT D^2 + a (v-b)^2 (2v+2b) ; quartic -> roots
import mpmath
num = lambda v: -R*T7*(v**2+2*b*v-b**2)**2 + a7*(v-b)**2*(2*v+2*b)
# polynomial coefficients in x = v/b (divide by b^4 * scale)
x = mpmath.mpf
# expand numerically via polyfit on exact quartic: use mpmath.taylor at 0
c = mpmath.taylor(lambda y: num(y*b)/b**3, 0, 4)[::-1]
sp = sorted([re(r) for r in polyroots(c, maxsteps=200, extraprec=200) if abs(im(r)) < 1e-25 and re(r) > 1])
print("spinodal x = v/b on (1,inf):", [mp.nstr(s, 10) for s in sp])
vmin, vmax = sp[0]*b, sp[1]*b
print("P_min/Pc", p(vmin)/Pc, " P_max/Pc", p(vmax)/Pc)

def outer_roots(ps):
    # P(v) = ps <=> ps (v-b) D - (R T D - a (v-b)) = 0, cubic in x
    g = lambda y: (ps*(y*b - b)*((y*b)**2 + 2*b*(y*b) - b**2) - (R*T7*((y*b)**2 + 2*b*(y*b) - b**2) - a7*(y*b - b)))
    cc = mpmath.taylor(g, 0, 3)[::-1]
    while cc and cc[0] == 0: cc = cc[1:]   # ps = 0: the cubic drops to a quadratic
    rs = sorted([re(r) for r in polyroots(cc, maxsteps=200, extraprec=200) if abs(im(r)) < 1e-20 and re(r) > 1])
    return [r*b for r in rs]

def area(ps):
    rs = outer_roots(ps)
    vl, vg = rs[0], rs[-1]
    return quad(lambda v: p(v) - ps, [vl, vmin, vmax, vg]), vl, vg, len(rs)

# Maxwell state
ps = findroot(lambda s: area(s)[0], (mpf('0.0113')*Pc, mpf('0.0116')*Pc), solver='anderson')
A, vl, vg, n = area(ps)
print("ps/Pc", ps/Pc, " omega", -log10(ps/Pc) - 1, " vl/b", vl/b, " vg/b", vg/b, " residual", A)
# uniqueness scan of the outer-root area function over (0, Pmax)
Pmax = p(vmax)
N = 400; signs = []
for k in range(1, N):
    s = Pmax*k/N
    signs.append(mpmath.sign(area(s)[0]))
changes = sum(1 for i in range(len(signs)-1) if signs[i] != signs[i+1])
print("levels scanned", N-1, "sign changes", changes, "first/last sign", signs[0], signs[-1])
# p_s <= 0: roots of P = ps in (b, inf) and sign of P - ps between them
for s in [mpf(0), p(vmin)/2, p(vmin)*mpf('0.99')]:
    rs = outer_roots(s)
    mid = (rs[0]+rs[-1])/2 if len(rs) >= 2 else None
    print("level ps/Pc=", mp.nstr(s/Pc, 6), "roots in (b,inf):", len(rs), " P-ps at midpoint", mp.nstr(p(mid)-s, 5) if mid else None)
