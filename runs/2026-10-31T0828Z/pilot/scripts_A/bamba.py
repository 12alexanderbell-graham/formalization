from sympy import *
t,q,j,s,l,k,z=symbols('t q j s l k z')
N=6
def trunc(e,v,n=N):
    e=expand(e)
    return sum(e.coeff(v,i)*v**i for i in range(n+1))
def mul(a,b,v): return trunc(a*b,v)
def inv(a,v):  # a = 1 + ...
    x=a-1; r=1; p=1
    for i in range(1,N+1):
        p=mul(p,-x,v); r+=p
    return trunc(r,v)
a=1+t-q*t**2/2+j*t**3/6+s*t**4/24+l*t**5/120
ia=inv(a,t)
G=integrate(ia,t)
chi=trunc(-G,t)     # int_t^0 ds/a
chi3=mul(mul(chi,chi,t),chi,t); chi5=mul(chi3,mul(chi,chi,t),t)
Sk=trunc(chi-k*chi3/6+k**2*chi5/120,t)
dl=mul(ia,Sk,t)
zt=trunc(ia-1,t)
# invert z(t): t = sum c_i z^i
cs=symbols('c1:7')
tz=sum(cs[i]*z**(i+1) for i in range(6))
def compose(f,g,v_f,v_g):
    # f polynomial in v_f, substitute g(v_g) truncated
    res=0; p=1
    for i in range(0,N+1):
        res+=f.coeff(v_f,i)*p
        p=mul(p,g,v_g)
    return trunc(res,v_g)
sol={}
for n in range(1,7):
    e=compose(zt,tz.subs(sol),t,z) if sol else compose(zt,tz,t,z)
    e=expand(e)-z
    cn=e.coeff(z,n)
    sol[cs[n-1]]=solve(cn.subs(sol),cs[n-1])[0]
    sol={kk:expand(v) for kk,v in sol.items()}
tzs=expand(tz.subs(sol))
dlz=compose(dl,tzs,t,z)
Dl=[factor(expand(dlz).coeff(z,n)) for n in range(1,6)]
dae=mul(dlz,inv((1+z)**2,z) if False else trunc(series(1/(1+z)**2,z,0,N+1).removeO(),z),z)
Da=[factor(expand(dae).coeff(z,n)) for n in range(1,6)]
import pickle
pickle.dump((Dl,Da,tzs,dlz),open('bamba_z.pkl','wb'))
for n in range(5): print('DL',n,Dl[n])
for n in range(5): print('DA',n,Da[n])
