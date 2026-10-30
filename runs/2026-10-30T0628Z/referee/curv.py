import sympy as sp
exec(open('/tmp/claude-0/ref/work/cosmo3.py').read().split("print(\"z(tau)")[0])
K=sp.symbols('K')  # K = k c^2/(a0^2 H0^2)
tau=z
for k in range(N): tau=sp.expand(tau-(comp(zt,t,tau,z,N)-z))
invA=inv1(A,t,N); I=sp.expand(sp.integrate(invA,(t,0,t)))
Iz=comp(I,t,tau,z,7)
I3=mul(mul(Iz,Iz,z,7),Iz,z,7); I5=mul(mul(I3,Iz,z,7),Iz,z,7)
S=sp.expand(Iz-K*I3/6+K**2*I5/120)
dL=mul(1+z,S,z,6); dA=mul(S,sum((-z)**k for k in range(7)),z,6)
R=sp.Rational
dLp=[1, -(-1+q)/2, -(1-q-3*q**2+j+K)/6, (2-2*q-15*q**2-15*q**3+5*j+10*q*j+s)/24+2*K*(1+3*q)/24,
 (-6+6*q+81*q**2+165*q**3+105*q**4)/120+(10*j**2-27*j-110*q*j-105*q**2*j)/120-(15*q*s+11*s+l)/120-5*K*(1+8*q+9*q**2-2*j)/120]
dAp=[1,-(3+q)/2,(11+7*q+3*q**2-j-K)/6,-(50+46*q+39*q**2+15*q**3-13*j-10*q*j-s)/24+2*K*(5+3*q)/24,
 (274+326*q+411*q**2+315*q**3+105*q**4)/120+(10*j**2-137*j-210*q*j-105*q**2*j-15*q*s-21*s-l)/120-5*K*(17+20*q+9*q**2-2*j)/120]
for n in range(5): print("dL^%d printed-correct:"%n, sp.factor(sp.expand(dLp[n]-dL.coeff(z,n+1))))
for n in range(5): print("dA^%d printed-correct:"%n, sp.factor(sp.expand(dAp[n]-dA.coeff(z,n+1))))
# R_D with curvature: r0/(D/a0) = sinn(chi)/(D/a0), chi=(c/(a0 H0)) I(tau), D/a0 = c tau/(a0 H0)  => (I - K I^3/6 + K^2 I^5/120)/tau
It=I; I3t=mul(mul(It,It,t,8),It,t,8); I5t=mul(mul(I3t,It,t,8),It,t,8)
Rt=sp.expand(sp.cancel(sp.expand(It-K*I3t/6+K**2*I5t/120)/t))
Rp=[1,R(1,2),(2+q-K)/6,(6+6*q+j-6*K)/24,(24+36*q+6*q**2+8*j-s-5*K*(7+2*q))/120,(24+48*q+18*q**2+4*q*j+12*j-2*s+24*l)/144-3*K*(15+10*q+j)/144]
for n in range(6): print("R^%d printed-correct:"%n, sp.factor(sp.expand(Rp[n]-Rt.coeff(t,n))))
