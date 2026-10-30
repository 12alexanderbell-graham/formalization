"""Independent check of reference.py against exact curved LambdaCDM (Om, Ok; OL=1-Om-Ok)."""
import sympy as sp, pickle
z,y,q,j,s,l,Ok = sp.symbols('z y q j s l Omega_k')
REF,REFY = pickle.load(open('ref.pkl','rb'))
A,Om,Okk,x = sp.symbols('A Omega_m Okk x')
OL = 1-Om-Okk
E = lambda aa: sp.sqrt(Om/aa**3 + Okk/aa**2 + OL)
adot = A*E(A)                      # H0=1
ders=[A, adot]
for n in range(2,6):
    ders.append(sp.diff(ders[-1],A)*adot)
at1 = [sp.simplify(d.subs(A,1)) for d in ders]
qv = -at1[2]; jv=at1[3]; sv=at1[4]; lv=at1[5]
print('q,j,s,l =', [sp.factor(v) for v in (qv,jv,sv,lv)])
subsd = {q:qv,j:jv,s:sv,l:lv,Ok:Okk}
Ez = sp.sqrt(Om*(1+z)**3+Okk*(1+z)**2+OL)
chi = sp.integrate(sp.series(1/Ez.subs(z,x),x,0,6).removeO(),(x,0,z))
r = chi + Okk*chi**3/6 + Okk**2*chi**5/120      # sinh(sqrt(Ok)chi)/sqrt(Ok)
look = sp.integrate(sp.series(1/((1+x)*Ez.subs(z,x)),x,0,6).removeO(),(x,0,z))
exact = dict(dL=(1+z)*r, dA=r/(1+z), chi=chi, r=r, lookback=look, Hz=Ez, lnDLoverZ=sp.log(sp.expand(sp.series((1+z)*r/z,z,0,5).removeO())))
for k_,e in exact.items():
    n = 5 if k_ in ('Hz','lnDLoverZ') else 6
    d = sp.expand(sp.series(e,z,0,n).removeO() - REF[k_].subs(subsd))
    print(k_, 'diff =', sp.simplify(d))
