import sympy as sp
x=sp.symbols('x')
for name,u,w in [('vdW',0,0),('RK',1,0),('PR',2,-1)]:
    f=x**3-3*x**2-3*(u+w)*x-(u**2+u*w-w)
    D=x**2+u*x+w
    A=D**2/((x-1)**2*(u+2*x))
    Ob=1/(x-1)-D/((x-1)**2*(u+2*x))
    Oa=sp.simplify(A*Ob); Z=x*Ob
    roots=[sp.N(r,30) for r in sp.Poly(f,x).real_roots() if sp.N(r)>1]
    xr=roots[0]
    print(name,'f=',sp.factor(f),'x=',xr)
    for nm,e in [('Zc',Z),('Ob',Ob),('Oa',Oa)]:
        # reduce mod f
        num,den=sp.fraction(sp.together(e))
        if sp.degree(f,x)>0 and sp.Poly(f,x).is_irreducible:
            inv=sp.invert(sp.Poly(den,x),sp.Poly(f,x))
            red=sp.rem(sp.Poly(num,x)*inv,sp.Poly(f,x))
            print(' ',nm,sp.N(e.subs(x,xr),15),'reduced:',red.as_expr())
        else:
            print(' ',nm,sp.nsimplify(sp.simplify(e.subs(x,sp.solve(f,x)[-1]))), sp.N(e.subs(x,xr),15))
