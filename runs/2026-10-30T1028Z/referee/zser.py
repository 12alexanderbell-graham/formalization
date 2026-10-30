import sympy as sp
q,j,s,l,Om,y,z,k=sp.symbols('q j s l Omega0 y z k')
DL=[1, sp.Rational(3,2)-q/2, -Om/6 - j/6 + q**2/2 - 5*q/6 + 2,
 Om*q/4 - 5*Om/12 + 5*j*q/12 - 7*j/24 - 5*q**3/8 + 7*q**2/8 - 4*q/3 + s/24 + sp.Rational(5,2),
 Om**2/120 + Om*j/12 - 3*Om*q**2/8 + 2*Om*q/3 - 29*Om/40 + j**2/12 - 7*j*q**2/8 + 3*j*q/4 - 19*j/40 - l/120 + 7*q**4/8 - 9*q**3/8 + 31*q**2/20 - q*s/8 - 39*q/20 + 3*s/40 + 3]
dly=sum(DL[n]*y**(n+1) for n in range(5)).subs(Om,1+k)
dlz=sp.expand(sp.series(dly.subs(y,z/(1+z)),z,0,6).removeO())
cz=[sp.expand(dlz.coeff(z,n+1)) for n in range(5)]
CS3=(2-2*q-15*q**2-15*q**3+5*j+10*q*j+s+2*k*(1+3*q))/24
CS4=(-6+6*q+81*q**2+165*q**3+105*q**4-110*q*j-105*q**2*j-15*q*s-27*j+10*j**2-11*s-l-5*k*(1+8*q+9*q**2-2*j))/120
print('z D3 CS - correct:', sp.factor(sp.expand(CS3-cz[3])))
print('z D4 CS - correct:', sp.factor(sp.expand(CS4-cz[4])))
dAz=sp.expand(sp.series(dlz/(1+z)**2,z,0,6).removeO())
ca=[sp.expand(dAz.coeff(z,n+1)) for n in range(5)]
CSA2=(11+7*q+3*q**2-j-k)/6
CSA3=-(50+46*q+39*q**2+15*q**3-13*j-10*q*j-s-2*k*(5+3*q))/24
CSA4=(274+326*q+411*q**2+315*q**3+105*q**4-210*q*j-105*q**2*j-15*q*s-137*j+10*j**2-21*s-l-5*k*(17+20*q+9*q**2-2*j))/120
for n,P in [(2,CSA2),(3,CSA3),(4,CSA4)]: print('z DA%d CS - correct:'%n, sp.factor(sp.expand(P-ca[n])))
print('DA1 correct', ca[1])
