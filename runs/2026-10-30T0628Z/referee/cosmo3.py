import sympy as sp, time
q,j,s,l,z,t,w=sp.symbols('q j s l z tau w')
N=6
def tr(e,x,n):
    e=sp.expand(e); return sp.Add(*[e.coeff(x,k)*x**k for k in range(n)])
def mul(a,b,x,n):
    a=sp.expand(a); b=sp.expand(b)
    ac=[a.coeff(x,k) for k in range(n)]; bc=[b.coeff(x,k) for k in range(n)]
    return sp.Add(*[sp.expand(sum(ac[i]*bc[k-i] for i in range(k+1)))*x**k for k in range(n)])
def comp(p,var,ser,x,n):
    # p(var) polynomial, substitute var=ser(x) (ser has no constant term), Horner with truncation
    p=sp.expand(p); deg=sp.degree(p,var); r=p.coeff(var,deg)
    for k in range(deg-1,-1,-1):
        r=sp.expand(mul(r,ser,x,n)+p.coeff(var,k))
    return r
def inv1(e,x,n):
    u=sp.expand(1-e); r=1; pw=1
    for k in range(1,n): pw=mul(pw,u,x,n); r+=pw
    return sp.expand(r)
A=1 - t - q/2*t**2 - j/6*t**3 + s/24*t**4 - l/120*t**5
zt=inv1(A,t,N)-1
print("z(tau)=",sp.collect(zt,t))
# Method 1: fixed-point reversion
tau=z
for k in range(N):
    tau=sp.expand(tau-(comp(zt,t,tau,z,N)-z))
tau1=tau
# Method 2: Lagrange inversion
f=zt.subs(t,w); phi=inv1(sp.expand(sp.cancel(f/w)),w,N)
tau2=0; pw=1
for n in range(1,N):
    pw=mul(pw,phi,w,N)
    tau2+=z**n/sp.factorial(n)*sp.diff(pw,w,n-1).subs(w,0)
print("methods agree:",sp.expand(tau1-tau2)==0)
Dz=[sp.expand(tau1.coeff(z,n+1)) for n in range(5)]
for n,c in enumerate(Dz): print("D^%d ="%n, c)
R=sp.Rational
printed_D4 = 1+2*q+3*q**2+R(5,2)*q**3+R(7,2)*q**4 - R(5,3)*q*j - R(7,8)*q**2*j - j + j**2/12 - q*s/8 - s/6 - l/120
printed=[1,-(1+q/2),1+q+q**2/2-j/6,-(1+R(3,2)*q+R(3,2)*q**2+R(5,8)*q**3-j/2-R(5,12)*q*j-s/24),printed_D4]
for n in range(5): print("printed - correct D^%d:"%n, sp.expand(printed[n]-Dz[n]))
dS={q:-1,j:1,s:1,l:1}; EdS={q:R(1,2),j:1,s:-R(7,2),l:R(35,2)}
print("dS  correct D0..4:",[c.subs(dS) for c in Dz]," printed D4:",printed_D4.subs(dS))
print("EdS correct D0..4:",[c.subs(EdS) for c in Dz]," printed D4:",printed_D4.subs(EdS))
invA=inv1(A,t,N)
Rs=sp.expand(sp.integrate(invA,(t,0,t))/t)
Rc=[sp.expand(Rs.coeff(t,n)) for n in range(6)]
for n,c in enumerate(Rc): print("R^%d ="%n,c)
R5p=(24+48*q+18*q**2+4*q*j+12*j-2*s+24*l)/144
print("printed R5 - correct:",sp.expand(R5p-Rc[5]))
I=sp.expand(sp.integrate(invA,(t,0,t)))
Iz=comp(I,t,tau1,z,7)
dL=mul(1+z,Iz,z,6)
dLc=[sp.expand(dL.coeff(z,n+1)) for n in range(5)]
dLp=[1, -(-1+q)/2, -(1-q-3*q**2+j)/6, (2-2*q-15*q**2-15*q**3+5*j+10*q*j+s)/24,
 (-6+6*q+81*q**2+165*q**3+105*q**4)/120+(10*j**2-27*j-110*q*j-105*q**2*j)/120-(15*q*s+11*s+l)/120]
for n in range(5): print("dL^%d correct:"%n,dLc[n],"| printed-correct:",sp.expand(dLp[n]-dLc[n]))
dA=mul(Iz,sum((-z)**k for k in range(7)),z,6)
dAc=[sp.expand(dA.coeff(z,n+1)) for n in range(5)]
dAp=[1,-(3+q)/2,(11+7*q+3*q**2-j)/6,-(50+46*q+39*q**2+15*q**3-13*j-10*q*j-s)/24,
 (274+326*q+411*q**2+315*q**3+105*q**4)/120+(10*j**2-137*j-210*q*j-105*q**2*j-15*q*s-21*s-l)/120]
for n in range(5): print("dA^%d printed-correct:"%n,sp.expand(dAp[n]-dAc[n]))
tau_bad=sum(printed[n]*z**(n+1) for n in range(5))
dLbad=mul(1+z,comp(I,t,tau_bad,z,7),z,6)
print("dL^4 via printed D-series minus correct:", sp.expand(dLbad.coeff(z,5)-dLc[4]))
print("dL dS:",[c.subs(dS) for c in dLc]," EdS:",[c.subs(EdS) for c in dLc])
import pickle; pickle.dump((Dz,dLc,Rc),open('/tmp/claude-0/ref/work/coef.pkl','wb'))
