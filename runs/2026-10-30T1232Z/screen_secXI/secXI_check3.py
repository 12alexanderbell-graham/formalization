"""Part 3: try to reproduce printed (11.42)-(11.45) under variants; upstream R (PRD 78 063504 Eq.33) test;
de Sitter degeneracy test of R."""
import sympy as sp
q,j,s,l,Om,eps=sp.symbols('q0 j0 s0 l0 Omega_M epsilon')
R0=-6*(1-q); Rd1=-6*(j-q-2); Rd2=-6*(s+q**2+8*q+6)
Rd3_true=-6*(l-s-2*(q+4)*j-6*(3*q+8)*q-24)
Rd3_print=-6*(l-s+2*(q+4)*j-6*(3*q+8)*q-24)
Hd0=-(1+q); Hdd0=j+3*q+2
f0,f2,f3=sp.symbols('f0 f2 f3')
def solve(Rd3,sg):
    E1=sp.Eq(1, Om+(f0-R0-6*Rd1*f2)/6)
    E2=sp.Eq(-Hd0, sp.Rational(3,2)*Om+(Rd1**2*f3+(Rd2-Rd1)*f2)/2)
    E3=sp.Eq(Hdd0,(Rd1**2*f3+(Rd2-Rd1)*f2+3*Om)*Rd1*f2/2-(3*Rd1*Rd2-Rd1**2)*f3/2
             -((Rd3-Rd2+sg*Hd0*Rd1)*f2-9*Om)/2)
    return sp.solve([E1,E2,E3],[f0,f2,f3],dict=True)[0]
L={q:sp.Rational(1,2)-sp.Rational(3,2)*(1-Om), j:1, s:1-sp.Rational(9,2)*Om, l:1+3*Om+sp.Rational(27,2)*Om**2}
Le={k:v*(1+eps) for k,v in L.items()}
D_=(3*(9*Om+74)*Om-556)*Om**2+16
p20=(64-6*Om*(9*Om+8))/D_/27
p30=(6*((81*Om-110)*Om+40)*Om+16)/D_/(243*Om**2)
print("printed (11.42),(11.43) numeric:",[(o,round(float(p20.subs(Om,o)),4),round(float(p30.subs(Om,o)),4)) for o in (0.041,0.25)])
def lin(e):
    return sp.factor(sp.cancel(sp.diff(sp.cancel(e.subs(Le)),eps).subs(eps,0)))
for name,(Rd3,sg) in {'correct':(Rd3_true,-1),'R3 misprint':(Rd3_print,-1),'+HdRd':(Rd3_true,1),'both':(Rd3_print,1)}.items():
    S=solve(Rd3,sg)
    e20=lin(S[f2]/S[f0]); e30=lin(S[f3]/S[f0])
    print(f"{name:12s} eta20/eps={e20}\n{'':12s} eta30/eps={e30}")
    print(f"{'':12s} numeric:",[(o,round(float(e20.subs(Om,o)),4),round(float(e30.subs(Om,o)),4)) for o in (0.041,0.25)],flush=True)
# printed-P/Q-only route: eta20 = (P2 Om+Q2)/(36 (P0 Om+Q0)), eta30=(P3 Om+Q3)/(216 (j-q-2)(P0 Om+Q0))
P0=(j-q-2)*l-(3*s+7*j+6*q**2+41*q+22)*s-((3*q+16)*j+20*q**2+64*q+12)*j-(3*q**4+25*q**3+96*q**2+72*q+20)
Q0=(q**2-j*q+2*q)*l+(3*q*s+(4*q+6)*j+6*q**3+44*q**2+22*q-12)*s+(2*j**2+(3*q**2+10*q-6)*j+17*q**3+52*q**2+54*q+36)*j+3*q**5+28*q**4+118*q**3+72*q**2-76*q-64
P2=9*s+6*j+9*q**2+66*q+42
Q2=-(6*(q+1)*s+(2*j-2*(1-q))*j+6*q**3+50*q**2+74*q+32)
P3=3*l+3*s-9*(q+4)*j-(45*q**2+78*q+12)
Q3=-(2*(1+q)*l+2*(j+q)*s-(2*j+4*q**2+12*q+6)*j-(30*q**3+84*q**2+78*q+24))
e20p=lin((P2*Om+Q2)/(36*(P0*Om+Q0))); e30p=lin((P3*Om+Q3)/(216*(j-q-2)*(P0*Om+Q0)))
print("from printed P0,Q0,P2,Q2,P3,Q3 only (R cancels): eta20/eps =",e20p,"; eta30/eps =",e30p)
print("  P0*Om+Q0 at LCDM:",sp.factor(sp.expand((P0*Om+Q0).subs(L))))
# R variants
Rrev=(j-q-2)*l-(3*s-2*j+6*q**2+50*q+40)*s+((3*q+10)*j+11*q**2+4*q+18)*j-(3*q**4+34*q**3+246*q+104)
Rup =(j-q-2)*l-(3*s-2*j+6*q**2+50*q+40)*s+((3*q+10)*j+11*q**2+4*q-18)*j-(3*q**4+34*q**3+246*q+104)
Rcor=(j-q-2)*l-(3*s-2*j+6*q**2+50*q+40)*s-((3*q+10)*j+11*q**2+4*q-18)*j-(3*q**4+34*q**3+180*q**2+246*q+104)
S=solve(Rd3_true,-1)
print("Rcor consistent with exact solution:",sp.cancel(S[f2]-(-(P2*Om+Q2)/Rcor/6)))
print("Rup - Rcor =",sp.factor(sp.expand(Rup-Rcor)),"; Rrev - Rcor =",sp.factor(sp.expand(Rrev-Rcor)))
dS={q:-1,j:1,s:1,l:1}
print("de Sitter (q,j,s,l)=(-1,1,1,1): Rcor=",Rcor.subs(dS)," Rup=",Rup.subs(dS)," Rrev=",Rrev.subs(dS))
Lam=3*(1-Om)
for nm,RR in (('review',Rrev),('upstream',Rup),('corrected',Rcor)):
    F0=(-6*(P0*Om+Q0)/RR).subs(L)
    print(f"LCDM F(R0) with {nm} R:",sp.factor(sp.cancel(F0)),"  [expected R0+2Lambda =",sp.expand(R0.subs(L)+2*Lam),"]",
          " at Om=0.25:",float(F0.subs(Om,0.25)),"vs",float((R0.subs(L)+2*Lam).subs(Om,0.25)))
