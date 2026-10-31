"""High-precision vdW coexistence table (reduced units), Maxwell construction.
Independent of run 1228Z's parametrization: solves the cubic for the three volumes at pressure ps
and bisects the equal-area residual in ps (the residual is monotone on (max(pmin,0), pmax))."""
import mpmath as mp
mp.mp.dps = 40
def coexist(Tr):
    Tr = mp.mpf(Tr)
    P = lambda v: 8*Tr/(3*v-1) - 3/v**2
    G = lambda v: 8*Tr/3*mp.log(3*v-1) + 3/v          # ∫P dv
    def roots(ps):
        r = mp.polyroots([3*ps, -(ps+8*Tr), 9, -3], maxsteps=400, extraprec=400)
        return sorted([x.real for x in r if abs(x.imag) < mp.mpf(10)**-25 and x.real > mp.mpf(1)/3])
    def F(ps):
        r = roots(ps); vl, vg = r[0], r[-1]
        return (G(vg)-G(vl)) - ps*(vg-vl)
    # spinodal pressures
    dP = lambda v: -24*Tr/(3*v-1)**2 + 6/v**3
    cand = mp.polyroots([4*Tr*27, -(36+4*Tr*27*0)+0, 0, 0], maxsteps=10) if False else None
    # bracket: F<0 near pmax, F>0 near max(pmin,0)
    vs = [mp.mpf(1)/3 + mp.mpf(k)/2000 for k in range(1, 20000)]
    ext = [vs[i] for i in range(1, len(vs)-1) if (P(vs[i])-P(vs[i-1]))*(P(vs[i+1])-P(vs[i])) <= 0]
    vmin = mp.findroot(dP, ext[0]); vmax = mp.findroot(dP, ext[1])
    lo, hi = max(P(vmin), mp.mpf(0)) + mp.mpf(10)**-30, P(vmax) - mp.mpf(10)**-30
    for _ in range(140):
        mid = (lo+hi)/2
        if F(mid) > 0: lo = mid
        else: hi = mid
    ps = (lo+hi)/2; r = roots(ps)
    return ps, r[0], r[-1], P(vmin), P(vmax)
if __name__ == '__main__':
    print('Tr  ps/Pc  vl/vc  vg/vc  omega_if_Tr=0.7  pmin  pmax')
    for Tr in ['0.5','0.6','0.7','0.8','0.85','0.9','0.95']:
        ps, vl, vg, pmin, pmax = coexist(Tr)
        print(Tr, mp.nstr(ps, 15), mp.nstr(vl, 15), mp.nstr(vg, 15), mp.nstr(-mp.log10(ps)-1, 12) if Tr=='0.7' else '', mp.nstr(pmin, 8), mp.nstr(pmax, 8))
