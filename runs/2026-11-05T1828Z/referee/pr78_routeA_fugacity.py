"""Referee route A (PR78): equal fugacity on the PR Z-cubic, closed-form Omega_a, Omega_b; unknown P_r."""
from mpmath import mp, mpf, sqrt, cbrt, log, log10, polyroots, findroot, re, im
mp.dps = 50
s2 = sqrt(2)
X = (-1 + cbrt(6*s2 + 8) - cbrt(6*s2 - 8)) / 3
Ob = X/(X + 3); Oa = 8*(5*X + 1)/(49 - 37*X)
Tr = mpf(7)/10
def k78(w): return mpf('0.379642') + mpf('1.48503')*w - mpf('0.164423')*w**2 + mpf('0.016666')*w**3
def k76(w): return mpf('0.37464') + mpf('1.54226')*w - mpf('0.26992')*w**2
def Zroots(A, B):
    c = [1, -(1 - B), A - 2*B - 3*B**2, -(A*B - B**2 - B**3)]
    return sorted(re(r) for r in polyroots(c, maxsteps=300, extraprec=300) if abs(im(r)) < mpf(10)**-35 and re(r) > B)
def lnphi(Z, A, B): return Z - 1 - log(Z - B) - A/(2*s2*B)*log((Z + (1 + s2)*B)/(Z + (1 - s2)*B))
def psat(alpha, guess=mpf('0.01')):
    def g(P):
        A = Oa*alpha*P/Tr**2; B = Ob*P/Tr; z = Zroots(A, B)
        return lnphi(z[0], A, B) - lnphi(z[-1], A, B)
    return findroot(g, (guess*mpf('0.95'), guess*mpf('1.05')), solver='anderson', tol=mpf(10)**-46)
if __name__ == '__main__':
    k = k78(1); al = (1 + k*(1 - sqrt(Tr)))**2; pr = psat(al); om = -log10(pr) - 1
    print("Omega_a", Oa, "\nOmega_b", Ob)
    print("kappa78(1)", k, "\nalpha(0.7)", al, "\nps/Pc", pr, "\nomega_out", om)
    print("margins ps/Pc to [0.00995,0.01005]:", mp.nstr(pr - mpf('0.00995'), 6), mp.nstr(mpf('0.01005') - pr, 6))
    print("margins omega to [0.9995,1.0005]:", mp.nstr(om - mpf('0.9995'), 6), mp.nstr(mpf('1.0005') - om, 6))
    print("omega window in pressure: need ps/Pc in", mp.nstr(mpf(10)**mpf('-2.0005'), 12), mp.nstr(mpf(10)**mpf('-1.9995'), 12),
          " margins", mp.nstr(pr - mpf(10)**mpf('-2.0005'), 6), mp.nstr(mpf(10)**mpf('-1.9995') - pr, 6))
    A = Oa*al*pr/Tr**2; B = Ob*pr/Tr; z = Zroots(A, B); print("Z roots", [mp.nstr(t, 12) for t in z])
    print("v_l/b, v_g/b", z[0]/B, z[-1]/B)
    # mutations / context
    for w in ['0.491', '0.8', '1.0', '1.2', '1.5', '2.0']:
        w = mpf(w); gs = mpf(10)**(-w - 1)
        print("w_in", w, " PR78 w_out", mp.nstr(-log10(psat((1 + k78(w)*(1 - sqrt(Tr)))**2, gs)) - 1, 10),
              " PR76 w_out", mp.nstr(-log10(psat((1 + k76(w)*(1 - sqrt(Tr)))**2, gs*mpf('1.3'))) - 1, 10))
    # rounding variants of the coefficients (sensitivity)
    for lab, kk in [("all +", mpf('0.379642') + mpf('1.48503') + mpf('0.164423') + mpf('0.016666')),
                    ("drop w^3", mpf('0.379642') + mpf('1.48503') - mpf('0.164423')),
                    ("w^3 sign -", mpf('0.379642') + mpf('1.48503') - mpf('0.164423') - mpf('0.016666')),
                    ("1.485 (5sf)", mpf('0.379642') + mpf('1.485') - mpf('0.164423') + mpf('0.016666')),
                    ("0.37464 const", mpf('0.37464') + mpf('1.48503') - mpf('0.164423') + mpf('0.016666'))]:
        pr2 = psat((1 + kk*(1 - sqrt(Tr)))**2, mpf('0.01') if kk < 1.8 else mpf('0.0049'))
        print(lab, "kappa", kk, " omega_out", mp.nstr(-log10(pr2) - 1, 10) if pr2 else "out of bracket")
    kstar = findroot(lambda kk: -log10(psat((1 + kk*(1 - sqrt(Tr)))**2)) - 2, (mpf('1.71'), mpf('1.72')), solver='anderson')
    print("kappa* (omega_out = 1 exactly)", kstar, " kappa78(1) - kappa*", mp.nstr(k - kstar, 6))
    # coefficient variants seen in the wild (Cantera PengRobinson.cpp code / Cantera header doc)
    for lab, kk in [("Cantera code 0.374642+1.487503-0.164423+0.016666", mpf('0.374642') + mpf('1.487503') - mpf('0.164423') + mpf('0.016666')),
                    ("Cantera doc 0.379642+1.487503-0.164423+0.016667", mpf('0.379642') + mpf('1.487503') - mpf('0.164423') + mpf('0.016667'))]:
        print(lab, "kappa", kk, " omega_out", mp.nstr(-log10(psat((1 + kk*(1 - sqrt(Tr)))**2)) - 1, 10))
