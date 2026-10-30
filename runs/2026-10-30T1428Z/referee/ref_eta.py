"""Referee: eta20, eta30 (11.42)-(11.45) and the (q0,j0)-only remark after (11.40)."""
import sympy as sp
q,j,s,l,Om,e=sp.symbols('q0 j0 s0 l0 Omega epsilon',real=True)
P0=(j-q-2)*l-(3*s+7*j+6*q**2+41*q+22)*s-((3*q+16)*j+20*q**2+64*q+12)*j-(3*q**4+25*q**3+96*q**2+72*q+20)
Q0=(q**2-j*q+2*q)*l+(3*q*s+(4*q+6)*j+6*q**3+44*q**2+22*q-12)*s+(2*j**2+(3*q**2+10*q-6)*j+17*q**3+52*q**2+54*q+36)*j+(3*q**5+28*q**4+118*q**3+72*q**2-76*q-64)
P2=9*s+6*j+9*q**2+66*q+42
Q2=-(6*(q+1)*s+(2*j-2*(1-q))*j+6*q**3+50*q**2+74*q+32)
P3=3*l+3*s-9*(q+4)*j-(45*q**2+78*q+12)
Q3=-(2*(1+q)*l+2*(j+q)*s-(2*j+4*q**2+12*q+6)*j-(30*q**3+84*q**2+78*q+24))
Rpr=(j-q-2)*l-(3*s-2*j+6*q**2+50*q+40)*s+((3*q+10)*j+11*q**2+4*q+18)*j-(3*q**4+34*q**3+246*q+104)
Rco=(j-q-2)*l-(3*s-2*j+6*q**2+50*q+40)*s-((3*q+10)*j+11*q**2+4*q-18)*j-(3*q**4+34*q**3+180*q**2+246*q+104)
L={q:sp.Rational(3,2)*Om-1,j:1,s:1-sp.Rational(9,2)*Om,l:1+3*Om+sp.Rational(27,2)*Om**2}
# (q0,j0)-only remark: fix q,j to LCDM, s,l free
QJ={q:L[q],j:1}
for nm,R in (("correct R",Rco),("printed R",Rpr)):
    print(nm,": with only (q0,j0) fixed to LCDM:")
    print("   P2 Om+Q2 =",sp.factor(sp.expand((P2*Om+Q2).subs(QJ))),"  P3 Om+Q3 =",sp.factor(sp.expand((P3*Om+Q3).subs(QJ))))
    print("   F(R0)/H0^2 - (R0+2Lambda)/H0^2 =",sp.factor(sp.simplify(-6*(P0*Om+Q0).subs(QJ)/R.subs(QJ)-(3*Om-6))))
# eta's (H0 = 1); epsilon scaling (11.41) with common eps
E={v:L[v]*(1+e) for v in (q,j,s,l)}
FL=3*Om-6   # F(R0)/H0^2 in LCDM
def etas(R):
    Fx=-6*(P0*Om+Q0)/R; F2=-(P2*Om+Q2)/(6*R); F3=-(P3*Om+Q3)/(36*(j-q-2)*R)
    out=[]
    for X in (F2,F3):
        r=sp.together((X/Fx).subs(E))
        c0=sp.simplify(r.subs(e,0)); c1=sp.factor(sp.simplify(sp.diff(r,e).subs(e,0)))
        out.append((c0,c1))
    return out
paper20=(64-6*Om*(9*Om+8))/((3*(9*Om+74)*Om-556)*Om**2+16)/27
paper30=6*(((81*Om-110)*Om+40)*Om+16)/((3*(9*Om+74)*Om-556)*Om**2+16)/(243*Om**2)
for nm,R in (("correct R",Rco),("printed R",Rpr)):
    (a0,a1),(b0,b1)=etas(R)
    print("==",nm)
    print("  eta20: O(1) =",a0,"  O(eps) coeff =",a1)
    print("  eta30: O(1) =",b0,"  O(eps) coeff =",b1)
    print("  ratio to printed (11.42):",sp.factor(sp.simplify(a1/paper20)))
    print("  ratio to printed (11.43):",sp.factor(sp.simplify(b1/paper30)))
    for om in (sp.Rational(41,1000),sp.Rational(1,4)):
        print(f"   Om={float(om)}: eta20/eps = {float(a1.subs(Om,om)):.4g}, eta30/eps = {float(b1.subs(Om,om)):.4g}")
for om in (sp.Rational(41,1000),sp.Rational(1,4)):
    print(f"printed formulas (11.42),(11.43) at Om={float(om)}: eta20/eps = {float(paper20.subs(Om,om)):.4g}, eta30/eps = {float(paper30.subs(Om,om)):.4g}")
print("printed (11.44): 0.15 (Om=0.041), -0.12 (Om=0.25); (11.45): 4 (0.041), -0.18 (0.25)")
print("printed denominator expanded:",sp.expand((3*(9*Om+74)*Om-556)*Om**2+16))
