"""Referee route A: PR equal fugacity in (A, B) form, reduced pressure as unknown.
Closed-form PR critical constants (X = [-1 + (6*sqrt2+8)^(1/3) - (6*sqrt2-8)^(1/3)]/3)."""
from mpmath import mp, mpf, sqrt, cbrt, log, log10, polyroots, findroot, re, im
mp.dps = 50
s2 = sqrt(2)
X = (-1 + cbrt(6*s2 + 8) - cbrt(6*s2 - 8)) / 3
Ob = X / (X + 3); Oa = 8*(5*X + 1) / (49 - 37*X); Zc = (1 - Ob) / 3  # triple root of the Z-cubic at the critical point
print("Omega_a", Oa, "Omega_b", Ob, "Z_c", Zc)

def kappa76(w): return mpf('0.37464') + mpf('1.54226')*w - mpf('0.26992')*w**2
def kappa78(w): return mpf('0.379642') + mpf('1.48503')*w - mpf('0.164423')*w**2 + mpf('0.016666')*w**3

def roots(A, B, u=2, w=-1):
    # generalized: Z^3 - (1 + B - uB) Z^2 + (A + wB^2 - uB - uB^2) Z - (AB + wB^2 + wB^3) = 0
    c = [1, -(1 + B - u*B), A + w*B**2 - u*B - u*B**2, -(A*B + w*B**2 + w*B**3)]
    rs = polyroots(c, maxsteps=200, extraprec=200)
    return sorted([re(r) for r in rs if abs(im(r)) < mpf(10)**-30 and re(r) > B])

def lnphi(Z, A, B, u=2, w=-1):
    d = sqrt(u*u - 4*w)
    if d == 0:  # vdW not used
        raise ValueError
    s1 = (u + d)/2; s2_ = (u - d)/2
    return Z - 1 - log(Z - B) - A/(B*d) * log((Z + s1*B)/(Z + s2_*B))

def psat(alpha, Tr=mpf(7)/10, u=2, w=-1, Oa=Oa, Ob=Ob):
    def g(Pr):
        A = Oa*alpha*Pr/Tr**2; B = Ob*Pr/Tr
        z = roots(A, B, u, w)
        if len(z) < 3: raise ValueError("not 3 roots at Pr=%s" % Pr)
        return lnphi(z[0], A, B, u, w) - lnphi(z[-1], A, B, u, w)
    # bracket by bisection on a scan then refine
    import mpmath
    lo, hi = mpf('1e-4'), None
    grid = [mpf(k)/2000 for k in range(1, 400)]
    prev = None
    for P in grid:
        try: v = g(P)
        except ValueError: continue
        if prev is not None and prev[1]*v < 0:
            return mpmath.findroot(g, (prev[0], P), solver='anderson', tol=mpf(10)**-45)
        prev = (P, v)
    raise RuntimeError

Tr = mpf(7)/10
for name, kap in [("PR76 kappa(1)", kappa76(1)), ("PR78 kappa(1)", kappa78(1))]:
    alpha = (1 + kap*(1 - sqrt(Tr)))**2
    pr = psat(alpha)
    om = -log10(pr) - 1
    print(name, "kappa", kap, "alpha", alpha)
    print("   ps/Pc", pr, " omega_out", om)
    print("   margins ps/Pc to [0.01135,0.01145]:", pr - mpf('0.01135'), mpf('0.01145') - pr)
    print("   margins omega to [0.9415,0.9425]:", om - mpf('0.9415'), mpf('0.9425') - om)
    print("   excess of ps over 10^-2:", pr/mpf('0.01') - 1)

# kappa(0.5) mutation
alpha = (1 + kappa76(mpf('0.5'))*(1 - sqrt(Tr)))**2
pr = psat(alpha); print("PR76 kappa(0.5): ps/Pc", pr, "omega", -log10(pr)-1)
# SRK form with PR kappa(1) (u=1,w=0): RK critical constants
Oa_rk = 1/(9*(cbrt(2)-1)); Ob_rk = (cbrt(2)-1)/3
alpha = (1 + kappa76(1)*(1 - sqrt(Tr)))**2
pr = psat(alpha, u=1, w=0, Oa=Oa_rk, Ob=Ob_rk); print("SRK form, PR76 kappa(1): ps/Pc", pr, "omega", -log10(pr)-1)
# kappa that reproduces omega=1 exactly in PR
def f(k):
    a = (1 + k*(1 - sqrt(Tr)))**2
    return -log10(psat(a)) - 2
kstar = findroot(f, (mpf('1.70'), mpf('1.75')), solver='anderson')
print("kappa reproducing omega=1 in PR:", kstar)
# omega_out over range (consistency curve)
for w in ['0', '0.2', '0.5', '0.8', '1.0', '1.2', '1.5']:
    w = mpf(w); a = (1 + kappa76(w)*(1 - sqrt(Tr)))**2; pr = psat(a)
    a2 = (1 + kappa78(w)*(1 - sqrt(Tr)))**2; pr2 = psat(a2)
    print("w_in", w, " PR76 w_out", mp.nstr(-log10(pr)-1, 8), " PR78 w_out", mp.nstr(-log10(pr2)-1, 8))
# PRSV (Stryjek-Vera 1986) kappa0 at omega = 1 (kappa1 term vanishes at Tr = 0.7)
k0 = mpf('0.378893') + mpf('1.4897153') - mpf('0.17131848') + mpf('0.0196554')
a = (1 + k0*(1 - sqrt(Tr)))**2; pr = psat(a)
print("PRSV kappa0(1)", k0, " omega_out", -log10(pr) - 1)
# near miss: same alpha but report omega to 3 decimals as 0.943 / ps to 0.0115
