import sympy as sp
x,y,z,q,j,s,l=sp.symbols('x y z q0 j0 s0 l0')
A = 1 - x - q/2*x**2 - j/6*x**3 + s/24*x**4 - l/120*x**5
chi = sp.integrate(sp.series(1/A,x,0,6).removeO(),x)
cs=sp.symbols('c1:6'); X=sum(cs[i]*z**(i+1) for i in range(5))
zx=sp.series(1/A-1,x,0,6).removeO()
eq=sp.expand(sp.series(zx.subs(x,X),z,0,6).removeO()-z)
sol=sp.solve([eq.coeff(z,k) for k in range(1,6)],cs,dict=True)[0]
Xs=X.subs(sol)
dl=sp.expand(sp.series((1+z)*chi.subs(x,Xs),z,0,6).removeO())
c4=dl.coeff(z,5); print('DL4 true', sp.factor(c4*120)/120)
pr=(-6+6*q+81*q**2+165*q**3+105*q**4+10*j**2-27*j-110*q*j-105*q**2*j-(15*q*s+11*s+l))/120
print('DL4 printed - true', sp.expand(pr-c4))
for k in range(1,4): print(k, sp.expand(dl.coeff(z,k+1)))
R=sp.expand(chi/x)
for k in range(6): print('R',k, sp.expand(R.coeff(x,k)))
print('R5 printed flat', sp.expand((24+48*q+18*q**2+4*q*j+12*j-2*s+24*l)/144))
da=sp.expand(sp.series(chi.subs(x,Xs)/(1+z),z,0,6).removeO())
print('DA4 true*120', sp.expand(120*da.coeff(z,5)))
pa=(274+326*q+411*q**2+315*q**3+105*q**4+10*j**2-137*j-210*q*j-105*q**2*j-15*q*s-21*s-l)/120
print('DA4 printed - true', sp.expand(pa-da.coeff(z,5)))
