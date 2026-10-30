"""C9 generator: z-series of d_L and d_A from the PROVED y-series (Checked.Cosmography.BambaK/BambaA).
Emits the polynomial W with (1+z)^5 [SY(z/(1+z)) - SZ(z)] = z^6 W(z) (and the d_A analogue), and
checks printed (Bamba et al. 2012 Eqs. 10.39-10.51, transcribed from typeset crops) vs correct."""
import sympy as sp
q,j,s,l,O,z,y,k=sp.symbols('q j s l Omega z y k')
R=sp.Rational
# correct y coefficients, copied from the Lean defs (Ω = Omega)
D1y=-R(1,2)*(-3+q)
D2y=R(1,6)*(12-5*q+3*q**2-j-O)
pD3y=R(1,24)*(52-20*q+21*q**2-15*q**3-7*j+10*q*j+s-2*O*(1+3*q))
pD4y=R(1,120)*(359-184*q+186*q**2-135*q**3+105*q**4+90*q*j-105*q**2*j-15*q*s-57*j+10*j**2+9*s-l-5*O*(17-6*q+9*q**2-2*j))
D3y=pD3y+(O-1)*(3*q-2)/6
D4y=pD4y+(O-1)**2/120+5*q*(O-1)/12
SY=y*(1+D1y*y+D2y*y**2+D3y*y**3+D4y*y**4)
# d_A y-series (correct)
DA1=-R(1,2)*(1+q); DA2=-R(1,6)*(-q-3*q**2+j+O)
pDA3=-R(1,24)*(-2*q+3*q**2+15*q**3-j-10*q*j-s+2*O)
pDA4=-R(1,120)*(1-6*q+9*q**2-15*q**3-105*q**4+10*q*j+105*q**2*j+15*q*s-3*j-10*j**2+s+l+5*O)
DA3=pDA3+q*(O-1)/4
DA4=pDA4+(O-1)*((O-1)+10*j-45*q**2+20*q)/120
SA=y*(1+DA1*y+DA2*y**2+DA3*y**3+DA4*y**4)
# printed z coefficients (k = K c^2/(H0^2 a0^2) = Omega - 1)
PL=[sp.Integer(1),-R(1,2)*(-1+q),-R(1,6)*(1-q-3*q**2+j+k),
    R(1,24)*(2-2*q-15*q**2-15*q**3+5*j+10*q*j+s+2*k*(1+3*q)),
    R(1,120)*(-6+6*q+81*q**2+165*q**3+105*q**4-110*q*j-105*q**2*j-15*q*s-27*j+10*j**2-11*s-l-5*k*(1+8*q+9*q**2-2*j))]
PA=[sp.Integer(1),-R(1,2)*(3+q),R(1,6)*(11+7*q+3*q**2-j-k),
    -R(1,24)*(50+46*q+39*q**2+15*q**3-13*j-10*q*j-s-2*k*(5+3*q)),
    R(1,120)*(274+326*q+411*q**2+315*q**3+105*q**4-210*q*j-105*q**2*j-15*q*s-137*j+10*j**2-21*s-l-5*k*(17+20*q+9*q**2-2*j))]
out={}
for name,S,P in [('L',SY,PL),('A',SA,PA)]:
    sz=sp.series(S.subs(y,z/(1+z)),z,0,6).removeO()
    c=[sp.expand(sz.coeff(z,n+1)) for n in range(5)]
    diffs=[sp.factor(sp.expand(P[n].subs(k,O-1)-c[n])) for n in range(5)]
    print(name,'printed - correct:',diffs)
    corr=[sp.expand(P[n].subs(k,O-1)-diffs[n]) for n in range(5)]
    SZ=z*sum(corr[n]*z**n for n in range(5))
    num=sp.expand(sp.cancel((S.subs(y,z/(1+z))-SZ)*(1+z)**5))
    W=sp.expand(sp.cancel(num/z**6))
    assert sp.expand(W*z**6-num)==0 and sp.Poly(W,z).degree()<=4
    out[name]=W
    print(name,'W =',W)
