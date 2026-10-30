import sympy as sp
def tr(e,x,n):
    e=sp.expand(e); return sum(e.coeff(x,k)*x**k for k in range(n))
def inv1(e,x,n):
    # 1/e for e=1+..., truncated
    e=sp.expand(e); u=1-e; r=1; p=1
    for k in range(1,n): p=tr(p*u,x,n); r+=p
    return sp.expand(r)

q,j,s,l,z,t,w=sp.symbols('q j s l z tau w')
N=6
# A(tau)=a(t)/a0 with tau=H0(t0-t), from (A1)
A=1 - t - q/2*t**2 - j/6*t**3 + s/24*t**4 - l/120*t**5
# z(tau)
zt=inv1(A,t,N)-1
# Method 1: iterative series reversion
tau=z
for k in range(N):
    tau=tr(tau - (tr(zt.subs(t,tau),z,N)-z),z,N)
tau1=sp.expand(tau)
# Method 2: Lagrange inversion: tau = sum_n z^n/n! d^{n-1}/dw^{n-1} (w/f(w))^n at w=0
f=zt.subs(t,w)
phi=inv1(sp.expand(f/w),w,N)
tau2=0
for n in range(1,N):
    g=tr(phi**n,w,n)
    tau2+= z**n/sp.factorial(n)*sp.diff(g,w,n-1).subs(w,0)
tau2=sp.expand(tau2)
print("methods agree:",sp.simplify(tau1-tau2)==0)
Dz=[sp.factor(sp.expand(tau1).coeff(z,n+1)) for n in range(5)]
for n,c in enumerate(Dz): print("D^%d ="%n, sp.expand(c))
printed_D4 = 1+2*q+3*q**2+sp.Rational(5,2)*q**3+sp.Rational(7,2)*q**4 - sp.Rational(5,3)*q*j - sp.Rational(7,8)*q**2*j - j + j**2/12 - q*s/8 - s/6 - l/120
printed=[1,-(1+q/2),1+q+q**2/2-j/6,-(1+sp.Rational(3,2)*q+sp.Rational(3,2)*q**2+sp.Rational(5,8)*q**3-j/2-sp.Rational(5,12)*q*j-s/24),printed_D4]
for n in range(5): print("printed - correct D^%d:"%n, sp.expand(printed[n]-Dz[n]))
dS={q:-1,j:1,s:1,l:1}; EdS={q:sp.Rational(1,2),j:1,s:-sp.Rational(7,2),l:sp.Rational(35,2)}
print("dS correct D4:",Dz[4].subs(dS)," printed:",printed_D4.subs(dS))
print("EdS correct D4:",Dz[4].subs(EdS)," printed:",printed_D4.subs(EdS))
# R_D (flat): r0/(D/a0) = (1/tau) int_0^tau dt'/A
invA=inv1(A,t,N)
R=sp.expand(sp.integrate(invA,(t,0,t))/t)
Rc=[sp.expand(R.coeff(t,n)) for n in range(6)]
for n,c in enumerate(Rc): print("R^%d ="%n,c)
R5p=(24+48*q+18*q**2+4*q*j+12*j-2*s+24*l)/144
print("printed R5 - correct:",sp.expand(R5p-Rc[5]))
# d_L flat: (1+z) * int_0^tau a0/a dtau'
I=sp.integrate(invA,(t,0,t))
dL=tr((1+z)*I.subs(t,tau1),z,6)
dLc=[sp.expand(dL.coeff(z,n+1)) for n in range(5)]
dLp=[1, -(-1+q)/2, -(1-q-3*q**2+j)/6, (2-2*q-15*q**2-15*q**3+5*j+10*q*j+s)/24,
 (-6+6*q+81*q**2+165*q**3+105*q**4)/120+(10*j**2-27*j-110*q*j-105*q**2*j)/120-(15*q*s+11*s+l)/120]
for n in range(5): print("dL^%d correct:"%n,dLc[n]," diff printed:",sp.expand(dLp[n]-dLc[n]))
dA=tr(I.subs(t,tau1)*sum((-z)**k for k in range(6)),z,6)
dAc=[sp.expand(dA.coeff(z,n+1)) for n in range(5)]
dAp=[1,-(3+q)/2,(11+7*q+3*q**2-j)/6,-(50+46*q+39*q**2+15*q**3-13*j-10*q*j-s)/24,
 (274+326*q+411*q**2+315*q**3+105*q**4)/120+(10*j**2-137*j-210*q*j-105*q**2*j-15*q*s-21*s-l)/120]
for n in range(5): print("dA^%d diff printed:"%n,sp.expand(dAp[n]-dAc[n]))
# What D4 would follow if the printed tau(z) series (with 7/2) were plugged in? effect on dL:
tau_bad=sum(printed[n]*z**(n+1) for n in range(5))
dLbad=tr((1+z)*I.subs(t,tau_bad),z,6)
print("dL^4 from printed D series - correct dL^4:", sp.expand(dLbad.coeff(z,5)-dLc[4]))
