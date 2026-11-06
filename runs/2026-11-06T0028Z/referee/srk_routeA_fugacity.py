"""Referee route A (SRK, Soave 1972): equal fugacity on the Z-cubic with closed-form
Omega_a = 1/(9(2^(1/3)-1)), Omega_b = (2^(1/3)-1)/3, Z_c = 1/3; mpmath 50 digits.
Also the context table omega_in -> omega_out and the kappa that reproduces omega = 1 exactly."""
from mpmath import mp, mpf, sqrt, log, log10, findroot, polyroots, re, im, cbrt
mp.dps = 50
c = cbrt(2) - 1
Oa, Ob = 1/(9*c), c/3
Tr = mpf(7)/10

def kappa(w):
    return mpf('0.480') + mpf('1.574')*w - mpf('0.176')*w**2

def zroots(A, B):
    rs = polyroots([1, -1, A - B - B**2, -A*B], maxsteps=400, extraprec=400)
    return sorted(re(r) for r in rs if abs(im(r)) < mpf(10)**-30 and re(r) > B)

def lnphi(Z, A, B):
    return Z - 1 - log(Z - B) - A/B*log(1 + B/Z)

def solve(kap, guess):
    alpha = (1 + kap*(1 - sqrt(Tr)))**2
    def AB(pr): return Oa*alpha*pr/Tr**2, Ob*pr/Tr
    def g(pr):
        A, B = AB(pr); z = zroots(A, B)
        return lnphi(z[0], A, B) - lnphi(z[-1], A, B)
    pr = findroot(g, (guess*mpf('0.98'), guess*mpf('1.02')), solver='anderson')
    A, B = AB(pr); z = zroots(A, B)
    # v/b = Z/B
    return alpha, pr, -log10(pr) - 1, z[0]/B, z[-1]/B, len(z)

if __name__ == '__main__':
    k1 = kappa(1)
    al, pr, om, vl, vg, n = solve(k1, mpf('0.0102'))
    print("Omega_a", Oa, "\nOmega_b", Ob)
    print("kappa(1)", k1, "\nalpha(0.7)", al, "\nps/Pc", pr, "\nomega_out", om, "\nvl/b", vl, "\nvg/b", vg, "\nnZroots", n)
    print("margins ps/Pc: lower", mp.nstr(pr - mpf('0.01015'), 6), " upper", mp.nstr(mpf('0.01025') - pr, 6))
    print("margins omega: lower", mp.nstr(om - mpf('0.9915'), 6), " upper", mp.nstr(mpf('0.9925') - om, 6))
    print("ps/Pc bounds from omega window: [10^-1.9925, 10^-1.9915] =", mp.nstr(mpf(10)**mpf('-1.9925'), 12), mp.nstr(mpf(10)**mpf('-1.9915'), 12))
    print("omega margins as ps/Pc: from ps_lo(omega<=0.9925)", mp.nstr(pr - mpf(10)**mpf('-1.9925'), 6), " to ps_hi(omega>=0.9915)", mp.nstr(mpf(10)**mpf('-1.9915') - pr, 6))
    # kappa that gives omega = 1 exactly
    ks = findroot(lambda k: solve(k, mpf('0.01'))[2] - 1, (k1 + mpf('0.01'), k1 + mpf('0.03')), solver='anderson')
    print("kappa* (omega_out = 1)", mp.nstr(ks, 12), " kappa(1) - kappa*", mp.nstr(k1 - ks, 6))
    print("omega_in -> omega_out (SRK, Soave 1972 kappa); and Graboski-Daubert 1978 kappa")
    gd = lambda w: mpf('0.48508') + mpf('1.55171')*w - mpf('0.15613')*w**2
    for w in ['0', '0.2', '0.5', '0.8', '1.0', '1.5', '2.0']:
        w = mpf(w); guess = mpf(10)**(-w - 1)
        o1 = solve(kappa(w), guess)[2]; o2 = solve(gd(w), guess)[2]
        print("  ", mp.nstr(w, 3), " Soave72:", mp.nstr(o1, 7), " (diff", mp.nstr(o1 - w, 4), ")   GD78:", mp.nstr(o2, 7), " (diff", mp.nstr(o2 - w, 4), ")")
