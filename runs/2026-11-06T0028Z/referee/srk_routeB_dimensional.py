"""Referee route B (SRK): dimensional RK form P = R T/(v-b) - a/(v^2 + b v) with arbitrary (R, ac, b);
critical point by Newton on the numerical 1st/2nd v-derivatives (no closed-form Omega's); Maxwell p_s
from the closed-form antiderivative R T ln(v-b) - (a/b) ln(v/(v+b)) (no quadrature, no fugacity);
spinodals; scan of the equal-area function for uniqueness; also a fluid with R < 0, Tc < 0."""
from mpmath import mp, mpf, sqrt, diff, findroot, log, log10, polyroots, re, im, taylor, sign
mp.dps = 45

def run(R, ac, b, T0):
    P = lambda a, T, v: R*T/(v - b) - a/(v**2 + b*v)
    Tc, vc = findroot(lambda T, v: [diff(lambda x: P(ac, T, x), v, 1), diff(lambda x: P(ac, T, x), v, 2)], (T0, 4*b))
    Pc = P(ac, Tc, vc)
    kap = mpf('0.480') + mpf('1.574')*1 - mpf('0.176')*1**2       # the Lean literal, same parse
    a7 = ac*(1 + kap*(1 - sqrt(mpf(7)/10)))**2; T7 = mpf(7)/10*Tc
    p = lambda v: P(a7, T7, v)
    F = lambda v: R*T7*log(v - b) - a7/b*log(v/(v + b))            # d/dv F = p(v) on v > b
    assert abs(diff(F, 5*b) - p(5*b)) < mpf(10)**-30 * abs(p(5*b)) + mpf(10)**-30
    def roots(ps):  # roots y = v/b > 1 of (v-b) v (v+b) (p(v) - ps) = 0, a cubic in v
        g = lambda y: R*T7*(y*b)*(y*b + b) - a7*(y*b - b) - ps*(y*b - b)*(y*b)*(y*b + b)
        cc = taylor(g, 0, 3)[::-1]
        while cc and cc[0] == 0: cc = cc[1:]
        return sorted(re(r)*b for r in polyroots(cc, maxsteps=400, extraprec=400) if abs(im(r)) < mpf(10)**-25 and re(r) > 1)
    def area(ps):
        r = roots(ps); return F(r[-1]) - F(r[0]) - ps*(r[-1] - r[0]), r
    ps = findroot(lambda s: area(s)[0], (mpf('0.0101')*Pc, mpf('0.0103')*Pc), solver='anderson')
    A, r = area(ps)
    print("R", R, " Tc", mp.nstr(Tc, 15), " vc/b", mp.nstr(vc/b, 15), " Zc", mp.nstr(Pc*vc/(R*Tc), 15),
          " Omega_b", mp.nstr(b*Pc/(R*Tc), 15), " Omega_a", mp.nstr(ac*Pc/(R*Tc)**2, 15))
    print("  ps/Pc", ps/Pc, "\n  omega", -log10(ps/Pc) - 1, "\n  vl/b", r[0]/b, "\n  vg/b", r[-1]/b,
          "\n  nroots", len(r), " area residual", mp.nstr(A, 3), " p(vl)-ps", mp.nstr(p(r[0]) - ps, 3), " p(vg)-ps", mp.nstr(p(r[-1]) - ps, 3))
    # spinodals: zeros of p' on (b, inf), numerator  -R T7 (v^2+bv)^2 + a7 (v-b)^2 (2v+b)
    num = lambda y: -R*T7*((y*b)**2 + b*b*y)**2 + a7*(y*b - b)**2*(2*y*b + b)
    allr = polyroots(taylor(num, 0, 4)[::-1], maxsteps=400, extraprec=400)
    sp = sorted(re(t) for t in allr if abs(im(t)) < mpf(10)**-20 and re(t) > 1)
    print("  all roots of p' numerator (v/b):", [mp.nstr(t, 8) for t in allr])
    Pmin, Pmax = p(sp[0]*b), p(sp[1]*b)
    print("  spinodal v/b", [mp.nstr(t, 10) for t in sp], " Pmin/Pc", mp.nstr(Pmin/Pc, 8), " Pmax/Pc", mp.nstr(Pmax/Pc, 8))
    N = 500; sg = [sign(area(Pmax*k/N)[0]) for k in range(1, N)]
    print("  scan of (0, Pmax) at", N - 1, "levels: sign changes", sum(1 for i in range(len(sg) - 1) if sg[i] != sg[i + 1]))
    return ps/Pc

x1 = run(mpf('8.314462618'), mpf('0.42748')*mpf('8.314462618')**2*mpf(190)**2/mpf('4.6e6'), mpf('2.98e-5'), mpf(190))
x2 = run(mpf('-1'), mpf('1'), mpf('1'), mpf('-0.2'))   # R < 0, Tc < 0 (R*Tc > 0)
x3 = run(mpf('2.5'), mpf('7'), mpf('0.3'), mpf('2'))
x4 = run(mpf('1'), mpf('-1'), mpf('1'), mpf('-0.2'))  # a_c < 0 (R*Tc < 0): P is minus an ordinary SRK isotherm, same ps/Pc
print("ps/Pc differences between fluids", mp.nstr(x1 - x2, 5), mp.nstr(x1 - x3, 5), mp.nstr(x1 - x4, 5))
