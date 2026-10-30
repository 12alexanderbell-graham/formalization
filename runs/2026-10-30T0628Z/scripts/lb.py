import sympy as sp
x,z,q,j,s,l=sp.symbols('x z q0 j0 s0 l0')
# x = H0 (t0 - t) >= 0 ; a/a0 = 1 - x - q/2 x^2 - j/6 x^3 + s/24 x^4 - l/120 x^5   (A1 with t-t0 = -x/H0)
a = 1 - x - q/2*x**2 - j/6*x**3 + s/24*x**4 - l/120*x**5
zx = sp.series(1/a - 1, x, 0, 6).removeO()
# invert: x = sum c_k z^k
cs=sp.symbols('c1:6'); X=sum(cs[i]*z**(i+1) for i in range(5))
eq=sp.expand(sp.series(zx.subs(x,X),z,0,6).removeO()-z)
sol=sp.solve([eq.coeff(z,k) for k in range(1,6)],cs,dict=True)[0]
for k in range(5): print('D',k,'=',sp.expand(sol[cs[k]]))
printed4=1+2*q+3*q**2+sp.Rational(5,2)*q**3+sp.Rational(7,2)*q**4-sp.Rational(5,3)*q*j-sp.Rational(7,8)*q**2*j-j+j**2/12-q*s/8-s/6-l/120
print('diff4', sp.expand(printed4-sol[cs[4]]))
