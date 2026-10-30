# Dust FLRW with curvature (Mattig) and closed de Sitter (a=cosh t), exact d_L vs y-series coefficients.
import sympy as sp
y,z,A=sp.symbols('y z A',positive=True)
q,j,s,l,Om=sp.symbols('q j s l Omega0')
D3c = Om*q/4 - 5*Om/12 + 5*j*q/12 - 7*j/24 - 5*q**3/8 + 7*q**2/8 - 4*q/3 + s/24 + sp.Rational(5,2)
D4c = Om**2/120 + Om*j/12 - 3*Om*q**2/8 + 2*Om*q/3 - 29*Om/40 + j**2/12 - 7*j*q**2/8 + 3*j*q/4 - 19*j/40 - l/120 + 7*q**4/8 - 9*q**3/8 + 31*q**2/20 - q*s/8 - 39*q/20 + 3*s/40 + 3
P3 = sp.Rational(1,24)*(52-20*q+21*q**2-15*q**3-7*j+10*q*j+s-2*Om*(1+3*q))
P4 = sp.Rational(1,120)*(359-184*q+186*q**2-135*q**3+105*q**4+90*q*j-105*q**2*j-15*q*s-57*j+10*j**2+9*s-l-5*Om*(17-6*q+9*q**2-2*j))
def cosmo_from_H(Hfun, K):
    # a0=1, H0=Hfun(1)
    H0=Hfun(1)
    der=[A]  # a^{(n)} as function of A
    for n in range(5): der.append(sp.simplify(A*Hfun(A)*sp.diff(der[-1],A)))
    c=[sp.simplify(der[n].subs(A,1)/H0**n) for n in range(6)]
    return dict(q=-c[2],j=c[3],s=c[4],l=c[5],Omega0=sp.simplify(1+K/H0**2))
def coeffs_from_dlz(dlz):  # H0 d_L(z) -> coefficients in y
    e=sp.series(dlz.subs(z,y/(1-y)),y,0,6).removeO()
    return [sp.nsimplify(sp.simplify(e.coeff(y,n+1))) for n in range(5)]
for Om_m in [sp.Rational(3,10), sp.Rational(2,1)]:
    Hf=lambda a: sp.sqrt(Om_m/a**3+(1-Om_m)/a**2)
    K=-(1-Om_m)   # Omega_k = -K/H0^2 = 1-Om_m, H0=1, a0=1
    p=cosmo_from_H(Hf,K)
    dl=2*(Om_m*z+(Om_m-2)*(sp.sqrt(1+Om_m*z)-1))/Om_m**2
    co=coeffs_from_dlz(dl)
    print('dust Om=',Om_m,p,'exact',co)
    print('   D3 exact',co[3],'derived',sp.simplify(D3c.subs(p)),'printed',sp.simplify(P3.subs(p)))
    print('   D4 exact',co[4],'derived',sp.simplify(D4c.subs(p)),'printed',sp.simplify(P4.subs(p)))
# closed de Sitter: a = cosh t /cosh t0 ... use H(a) with a0=1: H^2 = H0^2 (Ol + Ok/a^2), K=1 slicing; choose Ol=2, Ok=-1
Ol, Ok = sp.Integer(2), sp.Integer(-1)
Hf=lambda a: sp.sqrt(Ol+Ok/a**2)
p=cosmo_from_H(Hf, -Ok)  # K = -Ok*H0^2*a0^2, H0=1
# d_L numerically via quad, fit? Instead exact: chi = int dz/H(z), d_L=(1+z) sin(sqrt(K) chi)/sqrt(K)
w=sp.symbols('w')
Hz=sp.sqrt(Ol+Ok*(1+w)**2)
chis=sp.integrate(sp.series(1/Hz,w,0,6).removeO(),(w,0,z))
dl=(1+z)*sp.sin(chis)  # K=1 (H0=a0=1)
co=coeffs_from_dlz(dl)
print('closed dS Ol=2,Ok=-1',p,'exact',co)
print('   D3 exact',co[3],'derived',sp.simplify(D3c.subs(p)),'printed',sp.simplify(P3.subs(p)))
print('   D4 exact',co[4],'derived',sp.simplify(D4c.subs(p)),'printed',sp.simplify(P4.subs(p)))
