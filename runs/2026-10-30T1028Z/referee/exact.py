# Exact-model checks of the y-series coefficients (my derived vs printed).
import sympy as sp
y,t,T=sp.symbols('y t T')
q,j,s,l,Om=sp.symbols('q j s l Omega0')
D3c = Om*q/4 - 5*Om/12 + 5*j*q/12 - 7*j/24 - 5*q**3/8 + 7*q**2/8 - 4*q/3 + s/24 + sp.Rational(5,2)
D4c = Om**2/120 + Om*j/12 - 3*Om*q**2/8 + 2*Om*q/3 - 29*Om/40 + j**2/12 - 7*j*q**2/8 + 3*j*q/4 - 19*j/40 - l/120 + 7*q**4/8 - 9*q**3/8 + 31*q**2/20 - q*s/8 - 39*q/20 + 3*s/40 + 3
P3 = sp.Rational(1,24)*(52-20*q+21*q**2-15*q**3-7*j+10*q*j+s-2*Om*(1+3*q))
P4 = sp.Rational(1,120)*(359-184*q+186*q**2-135*q**3+105*q**4+90*q*j-105*q**2*j-15*q*s-57*j+10*j**2+9*s-l-5*Om*(17-6*q+9*q**2-2*j))
def params(a, t0, K):
    H=sp.simplify(sp.diff(a,t)/a).subs(t,t0)
    c=[sp.simplify((sp.diff(a,t,n)/(a*H**n)).subs(t,t0)) for n in range(6)]
    return dict(q=-c[2], j=c[3], s=c[4], l=c[5], Omega0=sp.simplify(1+K/(H**2*a.subs(t,t0)**2))), H
def check(name, a, t0, K, Sk, nint=None):
    p,H = params(a,t0,K)
    # exact: H0 d_L as function of emission time, then y
    a0=a.subs(t,t0)
    chi = sp.integrate(1/a.subs(t,T),(T,t,t0))
    dl = sp.simplify(H*a0*(a0/a)*Sk(chi))
    yt = 1 - a/a0
    # series in tau = t - t0, invert
    tau=sp.symbols('tau')
    yser = sp.series(yt.subs(t,t0+tau),tau,0,7).removeO()
    dser = sp.series(dl.subs(t,t0+tau),tau,0,7).removeO()
    cs=sp.symbols('c1:7'); tr=sum(cs[i]*y**(i+1) for i in range(6))
    e=sp.expand(sp.series(yser.subs(tau,tr),y,0,7).removeO())-y
    sol={}
    for n in range(1,7):
        sol[cs[n-1]]=sp.solve(sp.expand(e.coeff(y,n)).subs(sol),cs[n-1])[0]
    dy=sp.expand(sp.series(dser.subs(tau,tr.subs(sol)),y,0,6).removeO())
    co=[sp.nsimplify(sp.simplify(dy.coeff(y,n+1))) for n in range(5)]
    print(name, 'params', p, 'exact coeffs', co)
    print('   D3 exact',co[3],' derived',sp.simplify(D3c.subs(p)),' printed',sp.simplify(P3.subs(p)))
    print('   D4 exact',co[4],' derived',sp.simplify(D4c.subs(p)),' printed',sp.simplify(P4.subs(p)))
check('Milne a=t K=-1 t0=1', t, 1, -1, sp.sinh)
check('closed exp a=e^t K=1 t0=0', sp.exp(t), 0, 1, sp.sin)
check('open exp a=e^t K=-1 t0=0', sp.exp(t), 0, -1, sp.sinh)
check('closed dS a=cosh t K=1 t0=1', sp.cosh(t), 1, 1, sp.sin)
