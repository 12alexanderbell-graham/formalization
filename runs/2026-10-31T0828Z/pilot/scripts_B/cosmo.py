from sympy import *
import pickle
q,j,s,l,K,tau,y,z=symbols('q j s l K tau y z')
N=6  # keep orders < N  (powers 0..5)
def tr(e,v,n=N):
    e=expand(e); return sum(e.coeff(v,k)*v**k for k in range(n))
def mul(a,b,v): return tr(expand(a)*expand(b),v)
def compose(f,g,v,w):
    # f(v) with v->g(w), g has no constant term
    f=expand(f); res=0; gp=1
    for k in range(N):
        res+=f.coeff(v,k)*gp
        gp=tr(gp*g,w)
    return tr(res,w)
def recip(A,v):
    # 1/A, A=1+x
    x=expand(A-1); res=1; p=1
    for k in range(1,N):
        p=tr(p*(-x),v); res+=p
    return tr(res,v)
A=1+sum(c*(-tau)**n/factorial(n) for n,c in zip(range(1,6),[1,-q,j,s,l]))
invA=recip(A,tau)
zz=tr(invA-1,tau)
chi=sum(invA.coeff(tau,k)*tau**(k+1)/(k+1) for k in range(N-1))
SK=tr(chi-K*chi**3/6+K**2*chi**5/120,tau)
dL=mul(invA,SK,tau)
dA=mul(recip(invA,tau),SK,tau)
yy=mul(zz,recip(invA,tau),tau)
def revert(f,v,w):
    # f = c1 v + ..., c1=1 here; iterate v = w - (f - v)(v)
    g=w
    for it in range(N):
        g=tr(w-compose(expand(f-v),g,v,w),w)
    return g
tau_y=revert(yy,tau,y)
tau_z=revert(zz,tau,z)
res=dict(
 dLy=compose(dL,tau_y,tau,y), dAy=compose(dA,tau_y,tau,y),
 dLz=compose(dL,tau_z,tau,z), dAz=compose(dA,tau_z,tau,z), lookz=tau_z)
pickle.dump(res,open('res.pkl','wb'))
for nm,e in res.items():
    v=y if nm.endswith('y') else z
    print(nm)
    for k in range(1,6):
        print(' ',k, factor(expand(e).coeff(v,k)))
