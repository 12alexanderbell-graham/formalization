# Rational exact solutions of the Falkner-Skan equation f''' + f f'' + beta (1 - f'^2) = 0 with f' -> 1:
# f = u + c + sum_k a_k u^(-k), u = eta + d (run 2026-11-27T1228Z). Known member: beta = -1, f = u + 2/u.
import sympy as sp
u,c,b=sp.symbols('u c beta')
N=4
a=sp.symbols('a1:%d'%(N+1))
f=u+c+sum(a[k]*u**(-(k+1)) for k in range(N))
e=sp.expand((sp.diff(f,u,3)+f*sp.diff(f,u,2)+b*(1-sp.diff(f,u)**2))*u**(2*N+3))
eqs=sp.Poly(e,u).coeffs()
for s in sp.solve(eqs,[c,b]+list(a),dict=True):
    print(s)
