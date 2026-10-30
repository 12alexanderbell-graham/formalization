# Generates the polynomials for Work/Cosmography/BambaDLy.lean (flat d_L(y) to third order).
import sympy as sp
q,j,x,u,e=sp.symbols('q j x u e')
A=1-x-q*x**2/2-j*x**3/6            # a/a0 in x = H0 (t0 - t)
B2=1+x+(1+q/2)*x**2                # degree-2 truncation of 1/A
C=sp.expand((A*B2-1)/x**3)         # A*B2 = 1 + x^3 C
assert sp.expand(A*B2-1-x**3*C)==0
P=sp.integrate(B2.subs(x,u),(u,0,x)) # a0 H0 chi to x^3
D1=-sp.Rational(1,2)*(-3+q); D2=sp.Rational(1,6)*(12-5*q+3*q**2-j-1)
S=lambda y: y*(1+D1*y+D2*y**2)
G=lambda w: w*S(1-w)
diff=sp.expand(P-G(A))
for k in range(4): assert diff.coeff(x,k)==0, (k,diff.coeff(x,k))
W=sp.expand(diff/x**4); assert sp.expand(P-G(A)-x**4*W)==0
Q=sp.expand(sp.cancel((G(u+e)-G(u))/e))
assert sp.expand(G(u+e)-G(u)-e*Q)==0
# printed sign would fail: coefficient of x^3
Dp=-D2; diffp=sp.expand(P-(A*(1-A)*(1+D1*(1-A)+Dp*(1-A)**2)))
print('printed x^3 coeff:', sp.factor(diffp.coeff(x,3)), ' x^0..2:', [diffp.coeff(x,k) for k in range(3)])
f=lambda p: str(p).replace('**','^')
print('C :=',f(C)); print('P :=',f(sp.expand(P))); print('W :=',f(W)); print('Q :=',f(Q))
