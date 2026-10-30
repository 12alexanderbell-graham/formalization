import sympy as sp
q,j,s,l,m,k,x=sp.symbols('q j s l m k x')
A=1 - x - q*x**2/2 - j*x**3/6 + s*x**4/24 - l*x**5/120 + m*x**6/720  # a/a0 with x=H0 D, tau=-x
u=sp.integrate(sp.series(1/A,x,0,7).removeO(),(x,0,x))
F=sp.expand(sp.series(u - k*u**3/6 + k**2*u**5/120, x,0,7).removeO())
for n in range(1,7): print('R%d_D ='%(n-1), sp.factor(F.coeff(x,n)))
