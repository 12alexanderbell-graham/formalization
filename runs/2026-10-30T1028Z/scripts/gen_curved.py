# Generates the polynomials for Work/Cosmography/BambaCurved.lean (curved d_L(y) to fifth order).
# Every identity printed here is re-checked by `ring` in Lean.
import sympy as sp
q,j,s,l,k,x=sp.symbols('q j s l k x')
def tr(p,n=5): p=sp.expand(p); return sum(p.coeff(x,i)*x**i for i in range(n+1))
def hi(p,n=6):  # (p - tr(p))/x^n
    p=sp.expand(p); r=sp.expand((p-tr(p,n-1))/x**n); assert sp.expand(p-tr(p,n-1)-x**n*r)==0; return r
A=1-x-q*x**2/2-j*x**3/6+s*x**4/24-l*x**5/120          # = CCS.Apoly
B4=tr(sp.series(1/A,x,0,5).removeO(),4)
C5=hi(A*B4-1,5)
P5=sp.integrate(B4,(x,0,x)); P5q=sp.expand(P5/x)
M={1:sp.expand(P5)}; WM={}
for n in range(2,6):
    prod=sp.expand(P5*M[n-1]); M[n]=tr(prod); WM[n]=hi(prod)
F=sp.expand(M[1]-k*M[3]/6+k**2*M[5]/120)
N={1:sp.expand(1-A)}; WN={}
for n in range(2,6):
    prod=sp.expand(N[1]*N[n-1]); N[n]=tr(prod); WN[n]=hi(prod)
Om=1+k
D1=-sp.Rational(1,2)*(-3+q)
D2=sp.Rational(1,6)*(12-5*q+3*q**2-j-Om)
pD3=sp.Rational(1,24)*(52-20*q+21*q**2-15*q**3-7*j+10*q*j+s-2*Om*(1+3*q))
pD4=sp.Rational(1,120)*(359-184*q+186*q**2-135*q**3+105*q**4+90*q*j-105*q**2*j-15*q*s-57*j+10*j**2+9*s-l-5*Om*(17-6*q+9*q**2-2*j))
D3=pD3+(Om-1)*(3*q-2)/6
D4=pD4+(Om-1)**2/120+5*q*(Om-1)/12
Sp=sp.expand(N[1]+D1*N[2]+D2*N[3]+D3*N[4]+D4*N[5])
fin=sp.expand(A*Sp-F)
for i in range(6): assert sp.expand(fin.coeff(x,i))==0, i
Wf=hi(fin)
f=lambda p: str(sp.expand(p)).replace('**','^')
out={'B4':B4,'C5':C5,'P5':P5,'P5q':P5q}
for n in range(2,6): out[f'M{n}']=M[n]; out[f'WM{n}']=WM[n]
for n in range(2,6): out[f'N{n}']=N[n]; out[f'WN{n}']=WN[n]
out['Wf']=Wf
for kk,v in out.items(): print(kk, len(sp.Add.make_args(sp.expand(v))))
import json; json.dump({kk:f(v) for kk,v in out.items()}, open(__file__.replace('gen_curved.py','polys.json'),'w'))
