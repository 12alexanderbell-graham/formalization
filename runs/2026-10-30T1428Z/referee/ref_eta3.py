"""Referee: can a variant R (bracket sign, +-18, 180q^2 present/absent; upstream (33) = printed review R with -18)
explain the printed eta denominators?  eta20 = -N2'/(6 R_L F_L) if F(R0) is taken as R0+2Lambda while F'' uses R."""
import sympy as sp, itertools
q,j,s,l,Om=sp.symbols('q0 j0 s0 l0 Omega')
L={q:sp.Rational(3,2)*Om-1,j:1,s:1-sp.Rational(9,2)*Om,l:1+3*Om+sp.Rational(27,2)*Om**2}
target=-9*Om*(27*Om**3+276*Om**2-4*Om-8)/16
for sg,c18,c180 in itertools.product((1,-1),(18,-18),(0,180)):
    R=(j-q-2)*l-(3*s-2*j+6*q**2+50*q+40)*s+sg*((3*q+10)*j+11*q**2+4*q+c18)*j-(3*q**4+34*q**3+c180*q**2+246*q+104)
    RL=sp.factor(sp.expand(R.subs(L)))
    print(f"bracket sign {sg:+d}, const {c18:+d}, q^2 coeff {c180}: R_LCDM = {RL};  /target = {sp.factor(sp.cancel(RL/target))}")
Rup=(j-q-2)*l-(3*s-2*j+6*q**2+50*q+40)*s+((3*q+10)*j+11*q**2+4*q-18)*j-(3*q**4+34*q**3+246*q+104)
FL=3*Om-6
P0=(j-q-2)*l-(3*s+7*j+6*q**2+41*q+22)*s-((3*q+16)*j+20*q**2+64*q+12)*j-(3*q**4+25*q**3+96*q**2+72*q+20)
Q0=(q**2-j*q+2*q)*l+(3*q*s+(4*q+6)*j+6*q**3+44*q**2+22*q-12)*s+(2*j**2+(3*q**2+10*q-6)*j+17*q**3+52*q**2+54*q+36)*j+(3*q**5+28*q**4+118*q**3+72*q**2-76*q-64)
g=sp.factor(sp.expand(Rup.subs(L)*FL+6*(P0*Om+Q0).subs(L)))
print("UPSTREAM (33) R in LCDM: R*F(R0)/H0^2 + 6(P0 Om+Q0) =",g)
print("  real roots of the non-trivial factor:",[sp.N(r,6) for r in sp.Poly(sp.numer(sp.together(g/(Om-2))),Om).real_roots()])
