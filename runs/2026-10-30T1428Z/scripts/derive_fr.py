"""Run 1428Z: independent derivation of the F(R) cosmography system (Bamba et al. 2012 Sec. XI).
Model (paper's sign convention R = -6(Hdot + 2H^2)), field equations multiplied by F':
 E1: 3 F'(R) H^2 = rho + (F - R F')/2 - 3 H Rdot F''          (11.1)-(11.2)
 E2: -2 F'(R) Hdot = rho + Rddot F'' + Rdot (Rdot F''' - H F'') (11.5)
 rho = 3 H0^2 Om (a0/a)^3, rhodot = -3 H rho.
Closure: F'(R0) = 1, F''''(R0) = 0; E1 at t0, E2 at t0, d/dt E2 at t0."""
import sympy as sp
t=sp.symbols('t'); q,j,s,l,Om,H0=sp.symbols('q0 j0 s0 l0 Omega H0',real=True)
x0,x2,x3=sp.symbols('x0 x2 x3')
# H derivatives from a: a' = H a. Let a derivatives A_k = a0 H0^k c_k with c = 1,1,-q,j,s,l
A=[1,H0,-q*H0**2,j*H0**3,s*H0**4,l*H0**5]
h=sp.symbols('h0:5')
# a^(k+1) = sum binom(k,i) h_i a^(k-i)
eqs=[sp.Eq(A[k+1], sum(sp.binomial(k,i)*h[i]*A[k-i] for i in range(k+1))) for k in range(5)]
hs=sp.solve(eqs,h,dict=True)[0]
for i in range(5): print(f"h{i} =",sp.factor(hs[h[i]]))
h0,h1,h2,h3,h4=[hs[h[i]] for i in range(5)]
R0=-6*(h1+2*h0**2); R1=-6*(h2+4*h0*h1); R2=-6*(h3+4*h1**2+4*h0*h2); R3=-6*(h4+12*h1*h2+4*h0*h3)
for nm,e,pr in (('R0',R0,-6*H0**2*(1-q)),('R1',R1,-6*H0**3*(j-q-2)),('R2',R2,-6*H0**4*(s+q**2+8*q+6)),
                ('R3 vs printed (11.13)',R3,-6*H0**5*(l-s+2*(q+4)*j-6*(3*q+8)*q-24)),
                ('R3 vs sign-corrected',R3,-6*H0**5*(l-s-2*(q+4)*j-6*(3*q+8)*q-24))):
    print(nm,"diff:",sp.factor(sp.expand(e-pr)))
rho=3*H0**2*Om
E1=sp.expand(3*h0**2-(rho+(x0-R0)/2-3*h0*R1*x2))
E2=sp.expand(-2*h1-(rho+R2*x2+R1*(R1*x3-h0*x2)))
E3=sp.expand(-2*x2*R1*h1-2*h2-(-3*h0*rho+R3*x2+3*R1*R2*x3-h1*R1*x2-h0*R2*x2-h0*R1**2*x3))
sol=sp.solve([E1,E2,E3],[x0,x2,x3],dict=True)[0]
P0=(j-q-2)*l-(3*s+7*j+6*q**2+41*q+22)*s-((3*q+16)*j+20*q**2+64*q+12)*j-(3*q**4+25*q**3+96*q**2+72*q+20)
Q0=(q**2-j*q+2*q)*l+(3*q*s+(4*q+6)*j+6*q**3+44*q**2+22*q-12)*s+(2*j**2+(3*q**2+10*q-6)*j+17*q**3+52*q**2+54*q+36)*j+3*q**5+28*q**4+118*q**3+72*q**2-76*q-64
P2=9*s+6*j+9*q**2+66*q+42
Q2=-(6*(q+1)*s+(2*j-2*(1-q))*j+6*q**3+50*q**2+74*q+32)
P3=3*l+3*s-9*(q+4)*j-(45*q**2+78*q+12)
Q3=-(2*(1+q)*l+2*(j+q)*s-(2*j+4*q**2+12*q+6)*j-(30*q**3+84*q**2+78*q+24))
Rp=(j-q-2)*l-(3*s-2*j+6*q**2+50*q+40)*s+((3*q+10)*j+11*q**2+4*q+18)*j-(3*q**4+34*q**3+246*q+104)
# find denominator of my solution
num0,den0=sp.fraction(sp.factor(sol[x0]/H0**2))
print("x0/H0^2 =",sp.factor(sol[x0]/H0**2))
# test: Rc such that x0 = -6H0^2 (P0 Om+Q0)/Rc
Rc=sp.factor(sp.cancel(-6*H0**2*(P0*Om+Q0)/sol[x0]))
print("implied R (from x0) =",Rc)
Rc2=sp.factor(sp.cancel(-(P2*Om+Q2)/(sol[x2]*6*H0**2)))
print("implied R (from x2) =",Rc2)
Rc3=sp.factor(sp.cancel(-(P3*Om+Q3)/(sol[x3]*36*H0**4*(j-q-2))))
print("implied R (from x3) =",Rc3)
print("printed R - implied R =",sp.factor(sp.expand(Rp-Rc)))
