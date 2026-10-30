"""Reference cosmographic series to 5th order (sympy).
Conventions: a(t0)=1 (a0 set to 1; curvature k carries units 1/length^2 then),
 a(t0+D) = 1 + H D - q H^2 D^2/2 + j H^3 D^3/6 + s H^4 D^4/24 + l H^5 D^5/120,
 q=-a''a/a'^2, j=a'''a^2/a'^3, s=a''''a^3/a'^4, l=a^(5)a^4/a'^5,
 Omega_k = -k c^2/(H0^2 a0^2)  (so k c^2/H^2 = -Ok here).
 chi = c int dt/a ; r = S_k(chi) = sin(sqrt(k) chi)/sqrt(k) ; d_L=(1+z) r ; d_A = r/(1+z).
Everything is returned dimensionless: distances in units c/H0, times in 1/H0.
"""
import sympy as sp
z,y,T,Tp,q,j,s,l,Ok = sp.symbols('z y T Tp q j s l Omega_k')
NORD = 5           # highest power of z kept
N = NORD+1
H=1; c=1           # work in units c/H0 ; k c^2/H0^2 = -Ok
kk = -Ok
a = 1 - T - q/2*T**2 - j/6*T**3 + s/24*T**4 - l/120*T**5   # T = H0 (t0 - t)

def ser(e, v=z, n=N):
    return sp.expand(sp.series(e, v, 0, n).removeO())

zT = ser(1/a - 1, T)
bs = sp.symbols('b1:%d'%N)
Tz = sum(bs[i]*z**(i+1) for i in range(N-1))
eq = sp.expand(ser(zT.subs(T,Tz)) - z)
sol={}
for i in range(1,N):          # solve order by order (linear in b_i)
    e = eq.coeff(z,i).subs(sol)
    b = bs[i-1]
    sol[b] = sp.expand(sp.solve(e,b)[0])
Tz = sp.expand(Tz.subs(sol))           # H0 * lookback time
chiT = sp.integrate(ser(1/a.subs(T,Tp),Tp), (Tp,0,T))
chiz = ser(chiT.subs(T,Tz))            # H0 chi / c
r = ser(chiz - kk*chiz**3/6 + kk**2*chiz**5/120)
dL = ser((1+z)*r)
dA = ser(r/(1+z))
# H(z)/H0 : H = adot/a, adot = d a/dt = -H0 da/dT
HT = ser(-sp.diff(a,T)/a, T)
Hz = ser(HT.subs(T,Tz), z, N-1)   # H needs a^(6) at z^5 -> keep to z^4 only
# distance modulus: mu = 25 + 5 log10(c/H0 /Mpc) + 5 log10(z) + 5/ln10 * log(dL/z)
lnratio = ser(sp.log(sp.expand(dL/z)), z, N-1)   # ln(dL/z) to z^(NORD-1)
# deceleration etc as function of z also possible
def coeffs(e, v=z, n=N):
    return {i: sp.factor(sp.expand(e).coeff(v,i)) for i in range(0,n)}
def toy(e, n=N):   # rewrite series in z as series in y=z/(1+z)  (z=y/(1-y))
    return ser(e.subs(z, y/(1-y)), y, n)
REF = dict(dL=dL, dA=dA, chi=chiz, r=r, lookback=Tz, Hz=Hz, lnDLoverZ=lnratio)
NTRUNC = dict(Hz=N-1, lnDLoverZ=N-1)
REFY = {k_: toy(v, NTRUNC.get(k_,N)) for k_,v in REF.items()}
import pickle, os
pickle.dump((REF,REFY), open(os.path.join(os.path.dirname(os.path.abspath(__file__)),'ref.pkl'),'wb'))
if __name__=='__main__':
    for name,e in REF.items():
        print('==',name,'(z)')
        for i,cf in coeffs(e).items():
            if cf!=0: print('  z^%d:'%i, cf)
    for name,e in REFY.items():
        print('==',name,'(y)')
        for i,cf in coeffs(e,y).items():
            if cf!=0: print('  y^%d:'%i, cf)
