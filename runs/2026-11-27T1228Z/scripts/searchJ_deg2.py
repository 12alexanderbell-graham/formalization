import sympy as sp
t=sp.symbols('t')
p1,p2=sp.symbols('p1 p2'); g0,g1,g2,c=sp.symbols('g0 g1 g2 c')
P=1+p1*t+p2*t**2
H=-sp.diff(P,t)/(3*P)
R=sp.together(-6*(sp.diff(H,t)+2*H**2))
G=g0+g1*R+g2*R**2
expr=sp.diff(G,t,2)-H*sp.diff(G,t)+2*sp.diff(H,t)*G+c*P
num=sp.numer(sp.together(expr))
eqs=sp.Poly(sp.expand(num),t).coeffs()
print(len(eqs),flush=True)
for s in sp.solve(eqs,[p1,p2,g0,g1,g2,c],dict=True):
    print(s,flush=True)
