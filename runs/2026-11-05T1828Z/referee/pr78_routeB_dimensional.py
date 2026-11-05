"""Referee route B (PR78): dimensional PR with arbitrary (R, ac, b), critical point by Newton on the
numerical 1st/2nd derivatives, Maxwell p_s from the closed-form antiderivative of P (no quadrature,
no fugacity), uniqueness scan; also the R<0, Tc<0 case."""
from mpmath import mp, mpf, sqrt, diff, findroot, log, log10, polyroots, re, im, taylor, sign
mp.dps = 45
def run(R, ac, b, T0):
    s2 = sqrt(2)
    P = lambda a, T, v: R*T/(v - b) - a/(v**2 + 2*b*v - b**2)
    Tc, vc = findroot(lambda T, v: [diff(lambda x: P(ac, T, x), v, 1), diff(lambda x: P(ac, T, x), v, 2)], (T0, 4*b))
    Pc = P(ac, Tc, vc)
    kap = mpf('0.379642') + mpf('1.48503')*1 - mpf('0.164423')*1**2 + mpf('0.016666')*1**3
    a7 = ac*(1 + kap*(1 - sqrt(mpf(7)/10)))**2; T7 = mpf(7)/10*Tc
    p = lambda v: P(a7, T7, v)
    # antiderivative: R T ln(v-b) - a/(2 sqrt2 b) ln((v+b-sqrt2 b)/(v+b+sqrt2 b))
    F = lambda v: R*T7*log(v - b) - a7/(2*s2*b)*log((v + b - s2*b)/(v + b + s2*b))
    def roots(ps):
        g = lambda y: ps*(y*b - b)*((y*b)**2 + 2*b*b*y - b**2) - (R*T7*((y*b)**2 + 2*b*b*y - b**2) - a7*(y*b - b))
        cc = taylor(g, 0, 3)[::-1]
        while cc and cc[0] == 0: cc = cc[1:]
        return sorted(re(r)*b for r in polyroots(cc, maxsteps=300, extraprec=300) if abs(im(r)) < mpf(10)**-25 and re(r) > 1)
    def area(ps):
        r = roots(ps); return F(r[-1]) - F(r[0]) - ps*(r[-1] - r[0]), r
    ps = findroot(lambda s: area(s)[0], (mpf('0.0099')*Pc, mpf('0.0101')*Pc), solver='anderson')
    A, r = area(ps)
    print("R", R, "Tc", mp.nstr(Tc, 15), "vc/b", mp.nstr(vc/b, 15), "Zc", mp.nstr(Pc*vc/(R*Tc), 15))
    print("  ps/Pc", ps/Pc, "\n  omega", -log10(ps/Pc) - 1, "\n  vl/b", r[0]/b, " vg/b", r[-1]/b, " nroots", len(r), " resid", mp.nstr(A, 3))
    # spinodals and uniqueness scan
    num = lambda y: -R*T7*((y*b)**2 + 2*b*b*y - b**2)**2 + a7*(y*b - b)**2*(2*y*b + 2*b)
    sp = sorted(re(t) for t in polyroots(taylor(num, 0, 4)[::-1], maxsteps=300, extraprec=300) if abs(im(t)) < mpf(10)**-20 and re(t) > 1)
    Pmin, Pmax = p(sp[0]*b), p(sp[1]*b)
    print("  spinodal v/b", [mp.nstr(t, 8) for t in sp], " Pmin/Pc", mp.nstr(Pmin/Pc, 8), " Pmax/Pc", mp.nstr(Pmax/Pc, 8))
    N = 500; sg = [sign(area(Pmax*k/N)[0]) for k in range(1, N)]
    print("  scan levels", N - 1, " sign changes", sum(1 for i in range(len(sg) - 1) if sg[i] != sg[i + 1]))
    return ps/Pc
x1 = run(mpf('8.314462618'), mpf('2.3'), mpf('1.2e-4'), mpf(500))
x2 = run(mpf('-1'), mpf('1'), mpf('1'), mpf('-0.1'))   # R<0, Tc<0 (same R*Tc>0)
print("difference between the two fluids", mp.nstr(x1 - x2, 5))
