from sympy import *
L,r=symbols('L r',positive=True)
A=L*(r+1)-2*(r-1); B=r**2-1-2*L*r
xg=B/A; xl=B/(r*A)
tau=Rational(27,8)*A*B**2/((r-1)*(r-1-L)**2*(L*r-r+1)**2)
P=lambda x: 8*tau/x-27/(x+1)**2
print('E12', simplify(P(xl)-P(xg)))
p=P(xl)
print('E3', simplify(Rational(8,3)*tau*L+9/(xg+1)-9/(xl+1)-p*(xg-xl)/3))
print('p', factor(simplify(p)))
import mpmath
mpmath.mp.dps=40
ft=lambdify(L,tau.subs(r,exp(L)),'mpmath')
L0=mpmath.findroot(lambda t: ft(t)-mpmath.mpf(7)/10, 4.02)
print('L0',L0, 'r', mpmath.exp(L0))
fp=lambdify(L,p.subs(r,exp(L)),'mpmath')
print('p',fp(L0), 'dtau/dL', mpmath.diff(ft,L0), 'dp/dL', mpmath.diff(fp,L0))
