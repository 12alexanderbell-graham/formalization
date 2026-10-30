import sympy as sp
t,Om,H0=sp.symbols('t Omega_m H_0',positive=True)
# Route A: definitions (3) directly, with exact flat LCDM scale factor a(t)
A=((Om/(1-Om))**sp.Rational(1,3))*sp.sinh(sp.Rational(3,2)*sp.sqrt(1-Om)*H0*t)**sp.Rational(2,3)
# Route B: H as function of a, d/dt = a H d/da
a=sp.symbols('a',positive=True)
H=H0*sp.sqrt(Om*a**-3+1-Om)
ders=[a]
for k in range(6): ders.append(sp.simplify(a*H*sp.diff(ders[-1],a)))
vals=[sp.expand(sp.simplify((ders[k]/(a*H**k)).subs(a,1))) for k in range(7)]
names=['1','H/H','q','j','s','l','m']
print('Route B (derivatives of a via H(a)), (1/aH^n) d^n a/dt^n at a=1:')
for k in range(2,7):
    v=vals[k]*(-1 if k==2 else 1)
    print(names[k],'=',sp.factor(v), '=', sp.expand(v))
# Route C: Eq (4) of the paper with H derivatives wrt time
Hd=[H]
for k in range(5): Hd.append(sp.simplify(a*H*sp.diff(Hd[-1],a)))
r=[sp.simplify((Hd[k]/H**(k+1)).subs(a,1)) for k in range(6)]
q=-r[1]-1; j=r[2]-3*q-2; s=r[3]+4*j+3*q*(q+4)+6
l=r[4]-24-60*q-30*q**2-10*j*(q+2)+5*s
m=r[5]+10*j**2+120*j*(q+1)+3*(2*l+5*(24*q+18*q**2+2*q**3-2*s-q*s+8))
print('Route C via paper Eq.(4):',[sp.expand(x) for x in (q,j,s,l,m)])
# Route A check numerically at Om=0.3
t0=sp.asinh(sp.sqrt((1-Om)/Om))*2/(3*sp.sqrt(1-Om)*H0)
for n,name in [(5,'l'),(6,'m')]:
    e=sp.diff(A,t,n)/(A*(sp.diff(A,t)/A)**n)
    print('Route A numeric',name,'Om=0.3:',sp.N(e.subs({Om:sp.Rational(3,10),H0:1}).subs(t,t0.subs({Om:sp.Rational(3,10),H0:1}))), ' formula:', sp.N(vals[n].subs(Om,sp.Rational(3,10))))
