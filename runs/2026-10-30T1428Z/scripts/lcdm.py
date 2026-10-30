import sympy as sp
exec(open('cert.py').read().split("c1,c2,c3=")[0].replace("print(","(lambda *a,**k:None)("))
Rp=(j-q-2)*l-(3*s-2*j+6*q**2+50*q+40)*s+((3*q+10)*j+11*q**2+4*q+18)*j-(3*q**4+34*q**3+246*q+104)
L={q:sp.Rational(3,2)*Om-1, j:1, s:1-sp.Rational(9,2)*Om, l:1+3*Om+sp.Rational(27,2)*Om**2}
RpL=sp.factor(sp.expand(Rp.subs(L))); RcL=sp.factor(sp.expand(Rc.subs(L)))
PQ=sp.factor(sp.expand((P0*Om+Q0).subs(L)))
print("Rp_LCDM =",RpL); print("Rc_LCDM =",RcL); print("P0 Om+Q0 =",PQ)
x0L=sp.expand(-6*(1-(L[q]))+6*(1-Om))  # F(R0)/H0^2 = R0/H0^2 + 6(1-Om)
print("F(R0)/H0^2 =",x0L)
# printed claim: x0/(6) = -(PQ)/Rp  <=> x0*Rp + 6 PQ = 0
g=sp.factor(sp.expand(x0L*RpL+6*PQ)); print("x0*Rp+6PQ =",g)
print("roots of Rp_LCDM:",[sp.N(r) for r in sp.Poly(sp.expand(RpL),Om).all_roots()])
# de Sitter
dS={q:-1,j:1,s:1,l:1}; print("dS: Rp",Rp.subs(dS),"Rc",Rc.subs(dS),"PQ",sp.expand((P0*Om+Q0).subs(dS)))
