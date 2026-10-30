"""Referee: (i) standard-convention cross-check of dE2; (ii) which printed slips reproduce printed R;
(iii) paper's remark that (q0,j0) of LCDM alone force (11.40); (iv) eta20, eta30 (11.42)-(11.45)."""
import sympy as sp
q,j,s,l,Om,H0,e=sp.symbols('q0 j0 s0 l0 Omega H0 epsilon',real=True)
f0,f2,f3=sp.symbols('f0 f2 f3')
P0=(j-q-2)*l-(3*s+7*j+6*q**2+41*q+22)*s-((3*q+16)*j+20*q**2+64*q+12)*j-(3*q**4+25*q**3+96*q**2+72*q+20)
Q0=(q**2-j*q+2*q)*l+(3*q*s+(4*q+6)*j+6*q**3+44*q**2+22*q-12)*s+(2*j**2+(3*q**2+10*q-6)*j+17*q**3+52*q**2+54*q+36)*j+(3*q**5+28*q**4+118*q**3+72*q**2-76*q-64)
P2=9*s+6*j+9*q**2+66*q+42
Q2=-(6*(q+1)*s+(2*j-2*(1-q))*j+6*q**3+50*q**2+74*q+32)
P3=3*l+3*s-9*(q+4)*j-(45*q**2+78*q+12)
Q3=-(2*(1+q)*l+2*(j+q)*s-(2*j+4*q**2+12*q+6)*j-(30*q**3+84*q**2+78*q+24))
Rpr=(j-q-2)*l-(3*s-2*j+6*q**2+50*q+40)*s+((3*q+10)*j+11*q**2+4*q+18)*j-(3*q**4+34*q**3+246*q+104)
Rco=(j-q-2)*l-(3*s-2*j+6*q**2+50*q+40)*s-((3*q+10)*j+11*q**2+4*q-18)*j-(3*q**4+34*q**3+180*q**2+246*q+104)
# kinematics from definitions: H' = -H^2(1+q), H'' = H^3(j+3q+2), H''' = H^4(s-4j-3q(q+4)-6), H'''' = H^5(l-5s+10(q+2)j+30(q+2)q+24)
# (derived here by direct differentiation of H = a'/a with a-derivatives a0*H0^k*(1,1,-q,j,s,l))
t=sp.symbols('t'); a=1+H0*t-q*H0**2*t**2/2+j*H0**3*t**3/6+s*H0**4*t**4/24+l*H0**5*t**5/120
Hs=sp.series(sp.diff(a,t)/a,t,0,6).removeO()
Hk=[sp.expand(sp.diff(Hs,t,k).subs(t,0)) for k in range(5)]
Rk=[sp.expand(sp.diff(sp.expand(-6*(sp.diff(Hs,t)+2*Hs**2)),t,k).subs(t,0)) for k in range(4)]
R3pr=-6*H0**5*(l-s+2*(q+4)*j-6*(3*q+8)*q-24)
def system(sigma,R3,Fp=1):
    R0,R1,R2=Rk[0],Rk[1],Rk[2]
    E14=H0**2-(H0**2*Om/Fp+(f0-R0*Fp-6*H0*R1*f2)/(6*Fp))
    E15=-Hk[1]-(3*H0**2*Om/(2*Fp)+(R1**2*f3+(R2-H0*R1)*f2)/(2*Fp))
    E20=Hk[2]-((R1**2*f3+(R2-H0*R1)*f2+3*H0**2*Om)*R1*f2/(2*Fp**2)-(3*R1*R2-H0*R1**2)*f3/(2*Fp)
               -((R3-H0*R2+sigma*Hk[1]*R1)*f2-9*H0**3*Om)/(2*Fp))
    return [E14,E15,E20]
def solve(sys_):
    # E20 is quadratic in f2 (f2*f3 and f2^2 terms); E15 linear in f2,f3 -> eliminate f3, then f2
    sol=sp.solve(sys_,[f0,f2,f3],dict=True)
    return sol
print("Kinematics: Hdot,Hddot =",sp.factor(Hk[1]),",",sp.factor(Hk[2]))
for name,sigma,R3 in (("correct (sigma=-1, true R3)",-1,Rk[3]),("paper (11.20) +HdotRdot, true R3",+1,Rk[3]),
                      ("correct sigma, printed (11.13)",-1,R3pr),("paper (11.20) + printed (11.13)",+1,R3pr)):
    sols=solve(system(sigma,R3))
    print("==",name,": #solutions",len(sols))
    for so in sols:
        x0=sp.factor(so[f0]); x2=sp.factor(so[f2])
        d0=sp.factor(sp.fraction(sp.together(x0))[1])
        print("   F(R0) =",x0 if sp.count_ops(x0)<40 else "<long>")
        print("   F''(R0) =",x2 if sp.count_ops(x2)<60 else "<long>")
        print("   denominator(F(R0)) =",d0)
        print("   denominator vs printed R:",sp.factor(sp.cancel(d0/Rpr)), " vs correct R:",sp.factor(sp.cancel(d0/Rco)))
