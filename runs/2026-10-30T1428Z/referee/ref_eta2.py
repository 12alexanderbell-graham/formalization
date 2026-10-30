"""Referee: eta20/eta30 with the correctly parsed (11.43), numeric cross-check, and a search for
the input that reproduces the printed (11.42)-(11.43) (e.g. a wrong LCDM l0)."""
import sympy as sp
q,j,s,l,Om,e=sp.symbols('q0 j0 s0 l0 Omega epsilon',real=True)
P0=(j-q-2)*l-(3*s+7*j+6*q**2+41*q+22)*s-((3*q+16)*j+20*q**2+64*q+12)*j-(3*q**4+25*q**3+96*q**2+72*q+20)
Q0=(q**2-j*q+2*q)*l+(3*q*s+(4*q+6)*j+6*q**3+44*q**2+22*q-12)*s+(2*j**2+(3*q**2+10*q-6)*j+17*q**3+52*q**2+54*q+36)*j+(3*q**5+28*q**4+118*q**3+72*q**2-76*q-64)
P2=9*s+6*j+9*q**2+66*q+42
Q2=-(6*(q+1)*s+(2*j-2*(1-q))*j+6*q**3+50*q**2+74*q+32)
P3=3*l+3*s-9*(q+4)*j-(45*q**2+78*q+12)
Q3=-(2*(1+q)*l+2*(j+q)*s-(2*j+4*q**2+12*q+6)*j-(30*q**3+84*q**2+78*q+24))
D=(3*(9*Om+74)*Om-556)*Om**2+16
paper20=(64-6*Om*(9*Om+8))/D/27
paper30=(6*((81*Om-110)*Om+40)*Om+16)/D/(243*Om**2)
print("printed denominator factors:",sp.factor(D))
def eta(lL, label):
    L={q:sp.Rational(3,2)*Om-1,j:1,s:1-sp.Rational(9,2)*Om,l:lL}
    E={v:L[v]*(1+e) for v in (q,j,s,l)}
    # R cancels in F''/F and F'''/F: eta20 = (P2 Om+Q2)/(36(P0 Om+Q0)), eta30 = (P3 Om+Q3)/(216 (j-q-2)(P0 Om+Q0))
    r20=((P2*Om+Q2)/(36*(P0*Om+Q0))).subs(E); r30=((P3*Om+Q3)/(216*(j-q-2)*(P0*Om+Q0))).subs(E)
    c20=sp.factor(sp.simplify(sp.diff(r20,e).subs(e,0))); c30=sp.factor(sp.simplify(sp.diff(r30,e).subs(e,0)))
    print("==",label,": l0 =",lL)
    print("  (P0 Om+Q0)_LCDM =",sp.factor(sp.expand((P0*Om+Q0).subs(L))))
    print("  eta20/eps =",c20); print("  eta30/eps =",c30)
    print("  eta20 - printed(11.42):",sp.factor(sp.simplify(c20-paper20)))
    print("  eta30 - printed(11.43):",sp.factor(sp.simplify(c30-paper30)))
    for om in (0.041,0.25):
        # numeric check with finite epsilon
        ee=1e-7; num20=float(r20.subs({Om:om,e:ee}))/ee; num30=float(r30.subs({Om:om,e:ee}))/ee
        print(f"   Om={om}: eta20/eps={float(c20.subs(Om,om)):.4g} (finite-diff {num20:.4g}), eta30/eps={float(c30.subs(Om,om)):.4g} (finite-diff {num30:.4g});"
              f" printed formula: {float(paper20.subs(Om,om)):.4g}, {float(paper30.subs(Om,om)):.4g}")
eta(1+3*Om+sp.Rational(27,2)*Om**2,"correct LCDM l0 (11.39)")
eta(1+3*Om-sp.Rational(27,2)*Om**2,"sign-flipped l0 (Aviles-type slip)")
print("printed numbers: (11.44) eta20 = 0.15 eps (0.041), -0.12 eps (0.25); (11.45) eta30 = 4 eps (0.041), -0.18 eps (0.25)")
