"""Independent sympy re-derivation of Bamba-Capozziello-Nojiri-Odintsov (arXiv:1205.3421v3) Sec. XI.
Conventions (as stated in the paper): H=adot/a, q=-a''/(aH^2), j=a'''/(aH^3), s=a''''/(aH^4), l=a^(5)/(aH^5);
R = -6(Hdot+2H^2) (paper's negative-R convention, Eq. 11.6); kappa^2=1; rho_M = 3 H0^2 Om a^-3;
Friedmann: H^2 = (1/3)(rho_M/F' + rho_curv), rho_curv=(1/F')[(F-RF')/2 - 3 H Rdot F''] (11.1-11.2);
Raychaudhuri/master eq.: Hdot = -(1/(2F'))[rho_M + Rddot F'' + Rdot(Rdot F''' - H F'')] (11.5).
Units: H0 = 1 everywhere below (results are made dimensionless as in 11.21-11.24)."""
import sympy as sp
t=sp.symbols('t'); a=sp.Function('a')(t)
q,j,s,l,Om,H0=sp.symbols('q0 j0 s0 l0 Omega_M H0')
Hs=sp.Symbol('H')
H=a.diff(t)/a
# substitution a^(n) -> a H^n c_n
c=[1,1,-q,j,s,l]
def cosmo(expr):
    expr=expr.doit()
    for n in range(5,0,-1):
        expr=expr.subs(a.diff(t,n), a*Hs**n*c[n])
    return sp.expand(sp.simplify(expr))
print("== (10.6)-(10.9): derivatives of H")
dH=[cosmo(H.diff(t,n)) for n in range(1,5)]
printed=[-Hs**2*(1+q), Hs**3*(j+3*q+2), Hs**4*(s-4*j-3*q*(q+4)-6), Hs**5*(l-5*s+10*(q+2)*j+30*(q+2)*q+24)]
for n,(d,p) in enumerate(zip(dH,printed),1):
    print(f"d^{n}H/dt^{n} = {sp.factor(d)} ; printed-derived = {sp.simplify(p-d)}")
print("== (11.7)-(11.13): R and its derivatives, R=-6(Hdot+2H^2)")
Rt=-6*(H.diff(t)+2*H**2)
Rd=[cosmo(Rt.diff(t,n)) for n in range(0,4)]
Rd=[sp.expand(x.subs(Hs,1)) for x in Rd]   # H0=1
R0,R1,R2,R3=Rd
pr=[-6*(1-q), -6*(j-q-2), -6*(s+q**2+8*q+6), -6*(l-s+2*(q+4)*j-6*(3*q+8)*q-24)]
for n,(d,p) in enumerate(zip(Rd,pr)):
    print(f"R^({n})_0/H0^{n+2} derived = {sp.factor(d)} ; printed - derived = {sp.factor(sp.expand(p-d))}")
# check (11.9) operator form
Hf=sp.Function('Hf')(t)
R_H=-6*(Hf.diff(t)+2*Hf**2)
print("(11.7) diff:",sp.simplify(R_H.diff(t)-(-6*(Hf.diff(t,2)+4*Hf*Hf.diff(t)))))
print("(11.8) diff:",sp.simplify(R_H.diff(t,2)-(-6*(Hf.diff(t,3)+4*Hf*Hf.diff(t,2)+4*Hf.diff(t)**2))))
print("(11.9) diff:",sp.simplify(R_H.diff(t,3)-(-6*(Hf.diff(t,4)+4*Hf*Hf.diff(t,3)+12*Hf.diff(t)*Hf.diff(t,2)))))

print("== (11.18): differentiate master eq (11.5)")
Rf=sp.Function('R')(t); A=sp.Function('A')(t)
F=sp.Function('F')
F1,F2,F3,F4=[sp.Function(n) for n in ('F1','F2','F3','F4')]
# chain rule: d/dt F^(k)(R) = F^(k+1)(R) Rdot
def Fk(k): return [None,F1,F2,F3,F4][k](Rf)
rhoM=3*H0**2*Om*A**-3   # A=a(t)
N=rhoM+Rf.diff(t,2)*Fk(2)+Rf.diff(t)*(Rf.diff(t)*Fk(3)-Hf*Fk(2))
Hdot_expr=-N/(2*Fk(1))
dd=Hdot_expr.diff(t)
rep={sp.Derivative(Fk(k),t):Fk(k+1)*Rf.diff(t) for k in (1,2,3)}
rep[A.diff(t)]=A*Hf
dd=dd.subs({sp.Derivative(F1(Rf),t):F2(Rf)*Rf.diff(t)})
dd=sp.expand(dd.doit().subs({sp.Subs:0}))
# do chain rule manually by substituting
def chain(e):
    e=e.doit()
    for k in (3,2,1):
        e=e.replace(lambda x: isinstance(x,sp.Derivative) and x.expr==Fk(k), lambda x: Fk(k+1)*Rf.diff(t))
    e=e.subs(A.diff(t),A*Hf)
    return sp.expand(e)
dd=chain(Hdot_expr.diff(t))
Rd1,Rd2,Rd3=Rf.diff(t),Rf.diff(t,2),Rf.diff(t,3)
Hd=Hf.diff(t)
pr18=( (Rd1**2*Fk(3)+(Rd2-Hf*Rd1)*Fk(2)+rhoM)/(2*(Rd1*Fk(2))**-1*Fk(1)**2)
      -(Rd1**3*Fk(4)+(3*Rd1*Rd2-Hf*Rd1**2)*Fk(3))/(2*Fk(1))
      -((Rd3-Hf*Rd2+Hd*Rd1)*Fk(2)-9*H0**2*Om*Hf*A**-3)/(2*Fk(1)) )
print("printed(11.18) - derived =",sp.factor(sp.simplify(pr18-dd)))

print("== (11.3)-(11.4) curvature-fluid continuity (Bianchi) check")
rc=(1/Fk(1))*((F(Rf)-Rf*Fk(1))/2-3*Hf*Rd1*Fk(2))
wc=-1+(Rd2*Fk(2)+Rd1*(Rd1*Fk(3)-Hf*Fk(2)))/((F(Rf)-Rf*Fk(1))/2-3*Hf*Rd1*Fk(2))
lhs=chain(rc.diff(t).replace(lambda x: isinstance(x,sp.Derivative) and x.expr==F(Rf), lambda x: Fk(1)*Rd1))+3*Hf*(1+wc)*rc
rhs=3*H0**2*Om*Rd1*Fk(2)/Fk(1)**2*A**-3
print("(11.3) lhs-rhs simplifies to:",sp.simplify(lhs-rhs), " (expected 0 identically)")

print("== Solve (11.14),(11.15),(11.20) with F'(R0)=1, H0=1")
f0,f2,f3=sp.symbols('f0 f2 f3')   # F(R0), F''(R0), F'''(R0); f1=1
Hd0,Hdd0=dH[0].subs(Hs,1),dH[1].subs(Hs,1)
def solve_sys(R3use, sgnHdRd):
    E1=sp.Eq(1, Om + (f0-R0-6*R1*f2)/6)
    E2=sp.Eq(-Hd0, sp.Rational(3,2)*Om + (R1**2*f3+(R2-R1)*f2)/2)
    E3=sp.Eq(Hdd0, (R1**2*f3+(R2-R1)*f2+3*Om)*R1*f2/2 - (3*R1*R2-R1**2)*f3/2
              - ((R3use-R2+sgnHdRd*Hd0*R1)*f2-9*Om)/2)
    sol=sp.solve([E1,E2,E3],[f0,f2,f3],dict=True)
    return sol
sols=solve_sys(R3,-1)
print("number of solutions (correct eqs):",len(sols))
for sol in sols:
    for k in (f0,f2,f3): print(k,'=',sp.factor(sol[k]))
