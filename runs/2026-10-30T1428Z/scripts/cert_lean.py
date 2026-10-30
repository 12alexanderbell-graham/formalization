"""Emit linear_combination certificates (Lean syntax) for fR_values: H^3 * (goal.lhs - goal.rhs)
= c1*(L1.lhs-L1.rhs) + c2*(L2...) + c3*(L3...), with L1-L3 the closure equations in Lean form."""
import sympy as sp
exec(open('cert.py').read().split("c1,c2,c3=")[0].replace("print(","(lambda *a,**k:None)("))
c1,c2,c3=sp.symbols('c1 c2 c3')
targets={'T0':(Rc*x0, -6*H0**2*(P0*Om+Q0)),'T2':(Rc*(6*H0**2)*x2, -(P2*Om+Q2)),
         'T3':((j-q-2)*Rc*(6*H0**2)**2*x3, -(P3*Om+Q3))}
def lean(e):
    s=str(sp.expand(e)).replace('**','^').replace('q0','q').replace('j0','j').replace('s0','s').replace('l0','l').replace('Omega','Ω').replace('H0','H')
    return s
for nm,(L,Rr) in targets.items():
    T=sp.expand(H0**3*(L-Rr))
    expr=sp.expand(T-(c1*E1+c2*E2+c3*E3))
    eqs=[sp.expand(expr.coeff(v)) for v in (x0,x2,x3)]+[sp.expand(expr.subs({x0:0,x2:0,x3:0}))]
    sol=sp.solve(eqs,[c1,c2,c3],dict=True)[0]
    cs=[sp.factor(sol[c]) for c in (c1,c2,c3)]
    assert all(sp.fraction(sp.together(c))[1].free_symbols==set() for c in cs), cs
    print(nm,": linear_combination ("+lean(cs[0])+") * e1 + ("+lean(cs[1])+") * e2 + ("+lean(cs[2])+") * e3")
