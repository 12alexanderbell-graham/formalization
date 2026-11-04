from mpmath import mp,mpf,cbrt,sqrt,log,polyroots,findroot,log10,diff
mp.dps=40
c=cbrt(2); x=c*c+c+1
Ob=x*x/3-x-1; Oa=x/9
thc=9*Ob/x
th=mpf('0.7')**mpf('1.5')*thc
print('xc',x,'Ob',Ob,'Oa',Oa,'thc',thc,'th',th)
g=lambda x,t: t/(x-1)-1/(x*(x+1))
psi=lambda p,x,t: t*log(x-1)+log((x+1)/x)-p*x
def roots(p,t):
    # p(x-1)x(x+1) = t x(x+1) - (x-1)
    # p x^3 - p x  - t x^2 - t x + x - 1
    r=sorted([z.real for z in polyroots([p,-t,-p-t+1,-1]) if abs(z.imag)<mpf(10)**-30 and z.real>1])
    return r
def F(p,t):
    r=roots(p,t); return psi(p,r[-1],t)-psi(p,r[0],t)
def ps(t):
    return findroot(lambda p:F(p,t),mpf('0.001285'))
p=ps(th)
print('pi_s',p,'roots',roots(p,th))
ratio=p/sqrt(mpf('0.7'))*Oa/Ob**2
print('ps/Pc',ratio,'omega',-log10(ratio)-1)
# critical points of g: g' = -t/(x-1)^2 + (2x+1)/(x^2(x+1)^2)
from mpmath import polyroots
# numerator: (2x+1)(x-1)^2 - t x^2 (x+1)^2
import sympy as sp
X,T=sp.symbols('x t')
q=sp.expand((2*X+1)*(X-1)**2 - T*X**2*(X+1)**2)
print(sp.Poly(q,X).all_coeffs())
print([r for r in polyroots([float(cc.subs(T,th)) for cc in sp.Poly(q,X).all_coeffs()])])
# sensitivity dps/dth
e=mpf(10)**-8
print('dpi/dth',(ps(th+e)-ps(th-e))/(2*e))
def bis(t,lo,hi):
    for i in range(150):
        m=(lo+hi)/2
        if F(m,t)>0: lo=m
        else: hi=m
    return lo
print('F at',F(mpf('0.0012'),th),F(mpf('0.0013'),th))
p=bis(th,mpf('0.0012'),mpf('0.00135'))
r=roots(p,th)
ratio=p/sqrt(mpf('0.7'))*Oa/Ob**2
print('pi_s',p,'roots',r,'ps/Pc',ratio,'omega',-log10(ratio)-1)
e=mpf(10)**-6
print('dpi/dth',(bis(th+e,mpf('0.0012'),mpf('0.00135'))-bis(th-e,mpf('0.0012'),mpf('0.00135')))/(2*e))
