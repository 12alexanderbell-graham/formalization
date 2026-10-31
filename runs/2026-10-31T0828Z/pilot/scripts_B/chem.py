from sympy import *
R,a,b,T,v,u,w=symbols('R a b T v u w',positive=True)
def crit(uu,ww):
    P=R*T/(v-b)-a/(v**2+uu*b*v+ww*b**2)
    d1=diff(P,v); d2=diff(P,v,2)
    # solve for T from d1=0 and then v from d2
    Tsol=solve(d1,T)[0]
    e=simplify(d2.subs(T,Tsol)/ (a))
    x=symbols('x',positive=True)
    e=simplify(e.subs(v,x*b)*b**3)
    sols=[s for s in Poly(numer(together(e)),x).nroots() if abs(im(s))<1e-12]
    out=[]
    for xs in sols:
        xs=re(xs)
        if xs<=1: continue
        vc=xs*b
        Tc=Tsol.subs(v,vc)
        Pc=P.subs({T:Tc,v:vc})
        Zc=simplify(Pc*vc/(R*Tc)); Ob=simplify(b*Pc/(R*Tc)); Oa=simplify(a*Pc/(R*Tc)**2)
        out.append((xs,N(Zc,8),N(Ob,8),N(Oa,8)))
    return out
print('vdW',crit(0,0), 3/8, 1/8, 27/64)
print('RK',crit(1,0))
print('PR',crit(2,-1))
