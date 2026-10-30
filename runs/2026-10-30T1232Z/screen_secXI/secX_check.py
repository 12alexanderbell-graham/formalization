"""Sec. X (arXiv:1205.3421v3, Eqs. 10.12-10.68): cosmographic distance series, derived from scratch.
Units H0=c=a0=1, k := K c^2/(H0^2 a0^2) so Omega_0 = 1 + k. tau := t0 - t >= 0 (look-back time).
a(t0 - tau) = 1 - tau - q/2 tau^2 - j/6 tau^3 + s/24 tau^4 - l/120 tau^5 (from 10.10).
D = c(t0-t*) => tau = D. chi = int_0^D dtau/a ; r0 = chi - k chi^3/6 + k^2 chi^5/120 (10.30 with k).
d_L = (1+z) r0 (a0=1), d_A = r0/(1+z). y = z/(1+z)."""
import sympy as sp
q,j,s,l,k,z,D,tau,y,O0=sp.symbols('q0 j0 s0 l0 k z D tau y Omega0')
N=6
a=1-tau-q/2*tau**2-j/6*tau**3+s/24*tau**4-l/120*tau**5
opz=sp.series(1/a,tau,0,N).removeO()          # 1+z as series in D
print("(10.13) 1+z(D) coefficients:",[sp.factor(opz.coeff(tau,n)) for n in range(1,6)])
ZDpr=[1,1+q/2,1+q+j/6,1+sp.Rational(3,2)*q+q**2/4+j/3-s/24,1+2*q+sp.Rational(3,4)*q**2+q*j/6+j/2-s/12+l]
print("(10.15)-(10.19) printed - derived:",[sp.expand(ZDpr[n-1]-opz.coeff(tau,n)) for n in range(1,6)])
# invert z(D) -> D(z)
zD=sp.expand(opz-1)
Dz=z; 
for it in range(6):
    Dz=sp.expand(sp.series(z-(zD.subs(tau,Dz)-Dz),z,0,N).removeO())
Dzc=[sp.expand(Dz.coeff(z,n+1)) for n in range(5)]
Dzpr=[1,-(1+q/2),1+q+q**2/2-j/6,-(1+sp.Rational(3,2)*q+sp.Rational(3,2)*q**2+sp.Rational(5,8)*q**3-j/2-sp.Rational(5,12)*q*j-s/24),
      1+2*q+3*q**2+sp.Rational(5,2)*q**3+sp.Rational(7,2)*q**4-sp.Rational(5,3)*q*j-sp.Rational(7,8)*q**2*j-q*s/8-j+j**2/12-s/6-l/120]
print("(10.21)-(10.25) printed - derived:",[sp.factor(sp.expand(p-d)) for p,d in zip(Dzpr,Dzc)])
# chi(D)
chi=sp.integrate(sp.series(1/a,tau,0,N).removeO(),(tau,0,D))
chi=sp.expand(sp.series(chi,D,0,N+1).removeO())
print("(10.29) chi coefficients D^n/a0:",[sp.factor(chi.coeff(D,n)) for n in range(1,7)])
r0=sp.expand(sp.series(chi-k*chi**3/6+k**2*chi**5/120,D,0,N+1).removeO())
RDpr=[1,sp.Rational(1,2),(2+q-2*k)/6,(6+6*q+j-6*k)/24,(24+36*q+6*q**2+8*j-s-5*k*(7+2*q))/120,
      (24+48*q+18*q**2+4*q*j+12*j-2*s+24*l-3*k*(15+10*q+j))/144]
print("(10.32)-(10.37) printed - derived:",[sp.factor(sp.expand(RDpr[n]-r0.coeff(D,n+1))) for n in range(6)])
# luminosity / angular distances as series in z
r0z=sp.expand(sp.series(r0.subs(D,Dz),z,0,N).removeO())
dL=sp.expand(sp.series((1+z)*r0z,z,0,N).removeO()); dA=sp.expand(sp.series(r0z/(1+z),z,0,N).removeO())
DLc=[sp.expand(dL.coeff(z,n+1)) for n in range(5)]; DAc=[sp.expand(dA.coeff(z,n+1)) for n in range(5)]
DLpr=[1,-(-1+q)/2,-(1-q-3*q**2+j+k)/6,(2-2*q-15*q**2-15*q**3+5*j+10*q*j+s+2*k*(1+3*q))/24,
      (-6+6*q+81*q**2+165*q**3+105*q**4-110*q*j-105*q**2*j-15*q*s-27*j+10*j**2-11*s-l-5*k*(1+8*q+9*q**2-2*j))/120]
DApr=[1,-(3+q)/2,(11+7*q+3*q**2-j-k)/6,-(50+46*q+39*q**2+15*q**3-13*j-10*q*j-s-2*k*(5+3*q))/24,
      (274+326*q+411*q**2+315*q**3+105*q**4-210*q*j-105*q**2*j-15*q*s-137*j+10*j**2-21*s-l-5*k*(17+20*q+9*q**2-2*j))/120]
print("(10.39)-(10.44) printed - derived:",[sp.factor(sp.expand(p-d)) for p,d in zip(DLpr,DLc)])
print("(10.46)-(10.51) printed - derived:",[sp.factor(sp.expand(p-d)) for p,d in zip(DApr,DAc)])
# y-redshift: z = y/(1-y)
dLy=sp.expand(sp.series(dL.subs(z,y/(1-y)),y,0,N).removeO()); dAy=sp.expand(sp.series(dA.subs(z,y/(1-y)),y,0,N).removeO())
DLyc=[sp.expand(dLy.coeff(y,n+1).subs(k,O0-1)) for n in range(5)]; DAyc=[sp.expand(dAy.coeff(y,n+1).subs(k,O0-1)) for n in range(5)]
DLypr=[1,-(-3+q)/2,-(12-5*q+3*q**2-j-O0)/6,(52-20*q+21*q**2-15*q**3-7*j+10*q*j+s-2*O0*(1+3*q))/24,
       (359-184*q+186*q**2-135*q**3+105*q**4+90*q*j-105*q**2*j-15*q*s-57*j+10*j**2+9*s-l-5*O0*(17-6*q+9*q**2-2*j))/120]
DAypr=[1,-(1+q)/2,-(-q-3*q**2+j+O0)/6,-(-2*q+3*q**2+15*q**3-j-10*q*j-s+2*O0)/24,
       -(1-6*q+9*q**2-15*q**3-105*q**4+10*q*j+105*q**2*j+15*q*s-3*j-10*j**2+s+l+5*O0)/120]
print("(10.52)-(10.57) printed - derived:",[sp.factor(sp.expand(p-d)) for p,d in zip(DLypr,DLyc)])
print("   derived DL_y:",DLyc)
print("(10.58)-(10.63) printed - derived:",[sp.factor(sp.expand(p-d)) for p,d in zip(DAypr,DAyc)])
print("   derived DA_y:",DAyc)
# distance modulus (10.64)-(10.68): mu = 5/ln10 [ln z + sum M^n z^n], K=0, Hubble-free d_L
lnser=sp.expand(sp.series(sp.log(sp.expand(dL.subs(k,0)/z)),z,0,5).removeO())
Mc=[sp.expand(lnser.coeff(z,n)) for n in range(1,5)]
Mpr=[-(-1+q)/2,-(7-10*q-9*q**2+4*j)/24,(5-9*q-16*q**2-10*q**3+7*j+8*q*j+s)/24,
     (-469+1004*q+2654*q**2+3300*q**3+1575*q**4+200*j**2-1148*j-2620*q*j-1800*q**2*j-300*q*s-324*s-24*l)/2880]
print("(10.65)-(10.68) printed - derived:",[sp.factor(sp.expand(p-d)) for p,d in zip(Mpr,Mc)])
print("   derived M:",[sp.factor(m) for m in Mc])
# LCDM sanity check of M^n against exact d_L numerically
import mpmath as mp
Omv=0.3; qv=-1+1.5*Omv; jv=1; sv=1-4.5*Omv; lv=1+3*Omv+13.5*Omv**2
E=lambda zz: mp.sqrt(Omv*(1+zz)**3+1-Omv)
dLx=lambda zz:(1+zz)*mp.quad(lambda x:1/E(x),[0,zz])
sub={q:qv,j:jv,s:sv,l:lv}
for zz in (0.01,0.05):
    exact=mp.log(dLx(zz)/zz)
    ser_d=sum(float(Mc[n].subs(sub))*zz**(n+1) for n in range(4))
    ser_p=sum(float(Mpr[n].subs(sub))*zz**(n+1) for n in range(4))
    print(f"LCDM Om=0.3 z={zz}: ln(dL/z) exact={float(exact):.12e}, derived-series={ser_d:.12e}, printed-series={ser_p:.12e}")
