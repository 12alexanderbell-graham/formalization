import sympy as sp, time
q,j,s,l,k,x,y=sp.symbols('q j s l k x y')
A=1-x-q*x**2/2-j*x**3/6+s*x**4/24-l*x**5/120
Binv=sp.series(1/A,x,0,5).removeO()
B4=sp.expand(Binv)
P=sp.integrate(B4,(x,0,x))
F=lambda u: u-k*u**3/6+k**2*u**5/120
T=sp.expand(sp.series(F(P),x,0,7).removeO())
# solve for series S(y) coefficients: T(x) = w S(1-w), w = A(x)
D=sp.symbols('D1:5')
S=lambda yy: yy*(1+D[0]*yy+D[1]*yy**2+D[2]*yy**3+D[3]*yy**4)
expr=sp.expand(sp.series(T-A*S(1-A),x,0,6).removeO())
sol=sp.solve([expr.coeff(x,i) for i in range(1,6)],D,dict=True)[0]
for d in D: print(d, sp.factor(sol[d]))
# compare with printed (Omega0 = 1 + k)
O=1+k
pD3=sp.Rational(1,24)*(52-20*q+21*q**2-15*q**3-7*j+10*q*j+s-2*O*(1+3*q))
pD4=sp.Rational(1,120)*(359-184*q+186*q**2-135*q**3+105*q**4+90*q*j-105*q**2*j-15*q*s-57*j+10*j**2+9*s-l-5*O*(17-6*q+9*q**2-2*j))
print('pD3-D3', sp.factor(pD3-sol[D[2]]))
print('pD4-D4', sp.factor(pD4-sol[D[3]]))
print('pD4-D4 expanded', sp.expand(pD4-sol[D[3]]))
Sx=lambda yy: yy*(1+sol[D[0]]*yy+sol[D[1]]*yy**2+sol[D[2]]*yy**3+sol[D[3]]*yy**4)
t=time.time()
full=sp.expand(F(P)-A*Sx(1-A))
print('full terms',len(full.args), 'deg', sp.degree(full,x), time.time()-t)
for i in range(6): assert sp.expand(full.coeff(x,i))==0
