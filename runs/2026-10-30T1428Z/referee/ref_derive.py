"""Referee's independent derivation (series method, not the h_i recursion of derive_fr.py).
a(t) = Taylor polynomial at t0=0 with a0=1, coefficients from (H0,q,j,s,l); F = cubic Taylor
polynomial at R0 with F'(R0)=1 (unknowns f0=F(R0), f2=F''(R0), f3=F'''(R0)).
Equations, paper's convention R = -6(Hdot + 2H^2), kappa^2 = 1, rho = 3H0^2 Om a^-3:
 E1: 3F'H^2 = rho + (F - R F')/2 - 3 H Rdot F''          at t=0
 E2: -2F'Hdot = rho + Rddot F'' + Rdot(Rdot F''' - H F'')   at t=0 and its t-derivative at t=0.
Independent cross-check: derive the same equations from the STANDARD convention
 (R_s = 6(Hdot+2H^2), f(R_s) = -F(-R_s)) 3fH^2 = rho + (f_R R_s - f)/2 - 3H d(f_R)/dt,
 -2 f_R Hdot = rho + d^2(f_R)/dt^2 - H d(f_R)/dt."""
import sympy as sp
t,eps=sp.symbols('t epsilon')
q,j,s,l,Om,H0=sp.symbols('q0 j0 s0 l0 Omega H0',real=True)
f0,f2,f3,Fp=sp.symbols('f0 f2 f3 Fp')
N=6
a=1+H0*t-q*H0**2*t**2/2+j*H0**3*t**3/6+s*H0**4*t**4/24+l*H0**5*t**5/120
def ser(e,n=N): return sp.series(e,t,0,n).removeO()
H=ser(sp.diff(a,t)/a)
Hd=sp.diff(H,t)
R=sp.expand(-6*(Hd+2*H**2))
R0=R.subs(t,0)
dR=[sp.expand(sp.diff(R,t,k).subs(t,0)) for k in range(4)]
printed=[-6*H0**2*(1-q),-6*H0**3*(j-q-2),-6*H0**4*(s+q**2+8*q+6),-6*H0**5*(l-s+2*(q+4)*j-6*(3*q+8)*q-24)]
for k in range(4): print(f"d^{k}R/dt^{k} - printed(11.{10+k}) =",sp.factor(sp.expand(dR[k]-printed[k])))
print("d3R/dt3 / (-6H0^5) =",sp.expand(dR[3]/(-6*H0**5)))
X=sp.Symbol('X')
Fpoly=f0+Fp*(X-R0)+f2*(X-R0)**2/2+f3*(X-R0)**3/6
F =lambda r: Fpoly.subs(X,r)
F1=lambda r: sp.diff(Fpoly,X).subs(X,r)
F2=lambda r: sp.diff(Fpoly,X,2).subs(X,r)
F3=lambda r: sp.diff(Fpoly,X,3).subs(X,r)
rho=3*H0**2*Om*ser(1/a**3)
Rd=sp.diff(R,t); Rdd=sp.diff(R,t,2)
E1=ser(3*F1(R)*H**2-(rho+(F(R)-R*F1(R))/2-3*H*Rd*F2(R)),1)
E2=ser(-2*F1(R)*Hd-(rho+Rdd*F2(R)+Rd*(Rd*F3(R)-H*F2(R))),3)
eqs=[sp.expand(E1.subs(t,0)),sp.expand(E2.subs(t,0)),sp.expand(sp.diff(E2,t).subs(t,0))]
# standard-convention cross-check: f(Rs) = -F(-Rs)
Rs=-R
fR=lambda r: sp.diff(-Fpoly.subs(X,-X),X).subs(X,r)
fF=lambda r: (-Fpoly.subs(X,-X)).subs(X,r)
# exact (untruncated) comparison of the two conventions
S1=3*fR(Rs)*H**2-(rho+(fR(Rs)*Rs-fF(Rs))/2-3*H*sp.diff(fR(Rs),t))
S2=-2*fR(Rs)*Hd-(rho+sp.diff(fR(Rs),t,2)-H*sp.diff(fR(Rs),t))
U1=3*F1(R)*H**2-(rho+(F(R)-R*F1(R))/2-3*H*Rd*F2(R))
U2=-2*F1(R)*Hd-(rho+Rdd*F2(R)+Rd*(Rd*F3(R)-H*F2(R)))
print("standard-convention eqs identical (E1@0, E2@0, dE2/dt@0):",
      [sp.expand((U1-S1).subs(t,0))==0, sp.expand((U2-S2).subs(t,0))==0, sp.expand(sp.diff(U2-S2,t).subs(t,0))==0])
print("paper-form eqs equal the untruncated ones:",
      [sp.expand(eqs[0]-U1.subs(t,0))==0, sp.expand(eqs[1]-U2.subs(t,0))==0, sp.expand(eqs[2]-sp.diff(U2,t).subs(t,0))==0])
P0=(j-q-2)*l-(3*s+7*j+6*q**2+41*q+22)*s-((3*q+16)*j+20*q**2+64*q+12)*j-(3*q**4+25*q**3+96*q**2+72*q+20)
Q0=(q**2-j*q+2*q)*l+(3*q*s+(4*q+6)*j+6*q**3+44*q**2+22*q-12)*s+(2*j**2+(3*q**2+10*q-6)*j+17*q**3+52*q**2+54*q+36)*j+(3*q**5+28*q**4+118*q**3+72*q**2-76*q-64)
P2=9*s+6*j+9*q**2+66*q+42
Q2=-(6*(q+1)*s+(2*j-2*(1-q))*j+6*q**3+50*q**2+74*q+32)
P3=3*l+3*s-9*(q+4)*j-(45*q**2+78*q+12)
Q3=-(2*(1+q)*l+2*(j+q)*s-(2*j+4*q**2+12*q+6)*j-(30*q**3+84*q**2+78*q+24))
Rpr=(j-q-2)*l-(3*s-2*j+6*q**2+50*q+40)*s+((3*q+10)*j+11*q**2+4*q+18)*j-(3*q**4+34*q**3+246*q+104)
Rco=(j-q-2)*l-(3*s-2*j+6*q**2+50*q+40)*s-((3*q+10)*j+11*q**2+4*q-18)*j-(3*q**4+34*q**3+180*q**2+246*q+104)
def solve(eqs,fp=1):
    return sp.solve([e.subs(Fp,fp) for e in eqs],[f0,f2,f3],dict=True)[0]
sol=solve(eqs)
x0,x2,x3=[sp.factor(sol[v]) for v in (f0,f2,f3)]
den=sp.fraction(sp.together(x0))[1]
print("denominator of F(R0):",sp.factor(den))
chk=[sp.simplify(x0-(-6*H0**2*(P0*Om+Q0)/Rco)),
     sp.simplify(x2-(-(P2*Om+Q2)/(Rco*6*H0**2))),
     sp.simplify(x3-(-(P3*Om+Q3)/((j-q-2)*Rco*36*H0**4)))]
print("F(R0),F'',F''' match P/Q with correctR:",chk)
print("Rco - Rpr =",sp.factor(sp.expand(Rco-Rpr)))
# --- ΛCDM, derived independently from H^2 = H0^2(Om a^-3 + 1-Om): a-derivatives via ODE
A=sp.Function('A')
# a' = H0 a sqrt(Om a^-3 + 1 - Om); iterate derivatives symbolically in a
av=sp.Symbol('av',positive=True)
ad=H0*av*sp.sqrt(Om/av**3+1-Om)
ders=[av,ad]
for k in range(4): ders.append(sp.simplify(sp.diff(ders[-1],av)*ad))
vals=[sp.simplify(d.subs(av,1)) for d in ders]
L={q:sp.simplify(-vals[2]/H0**2),j:sp.simplify(vals[3]/H0**3),s:sp.simplify(vals[4]/H0**4),l:sp.simplify(vals[5]/H0**5)}
print("LCDM (q,j,s,l):",[sp.expand(L[v]) for v in (q,j,s,l)])
FL=sp.expand((R0+6*H0**2*(1-Om)).subs(L))
print("LCDM F(R0)=R0+2Lambda =",FL)
eL=[sp.expand(e.subs(L).subs({f0:FL,f2:0,f3:0,Fp:1})) for e in eqs]
print("LCDM satisfies E1,E2,dE2:",eL)
RprL=sp.factor(sp.expand(Rpr.subs(L))); RcoL=sp.factor(sp.expand(Rco.subs(L)))
PQL=sp.factor(sp.expand((P0*Om+Q0).subs(L)))
print("printedR_LCDM =",RprL," correctR_LCDM =",RcoL," (P0 Om+Q0)_LCDM =",PQL)
print("P2Om+Q2, P3Om+Q3 at LCDM:",sp.expand((P2*Om+Q2).subs(L)),sp.expand((P3*Om+Q3).subs(L)))
g=sp.factor(sp.expand(RprL*FL+6*H0**2*PQL))
print("printedR*F + 6H0^2(P0 Om+Q0) at LCDM =",g)
print("correctR*F + 6H0^2(P0 Om+Q0) at LCDM =",sp.expand(RcoL*FL+6*H0**2*PQL))
print("real roots of printedR_LCDM:",[sp.N(r,8) for r in sp.Poly(sp.numer(sp.together(RprL)),Om).real_roots()])
print("real roots of correctR_LCDM:",[sp.N(r,8) for r in sp.Poly(sp.numer(sp.together(RcoL)),Om).real_roots()] if RcoL.has(Om) else RcoL)
print("disc(909Om^2-1170Om+416) =",1170**2-4*909*416)
# printed F(R0) value with printed R at Om=0.25, 0.041 vs truth
for om in (sp.Rational(1,4),sp.Rational(41,1000)):
    sub={Om:om,H0:1}
    print(f"Om={om}: true F(R0)/H0^2 =",sp.N(FL.subs(sub)),"printed-formula F(R0)/H0^2 =",sp.N((-6*PQL/RprL).subs(sub)))
# --- dS check (Om=0): q=-1,j=s=l=1
dS={q:-1,j:1,s:1,l:1}
print("de Sitter: printedR",Rpr.subs(dS)," correctR",Rco.subs(dS)," P0*0+Q0",Q0.subs(dS))
import pickle
pickle.dump({'eqs':eqs,'L':L},open('/tmp/claude-0/referee/eqs.pkl','wb'))
