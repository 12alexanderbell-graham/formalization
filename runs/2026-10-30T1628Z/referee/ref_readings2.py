# Referee: further attempts to reproduce printed (11.42)-(11.43).
import sympy as sp
O,e,q,j,s,l,wq,wj = sp.symbols('Omega epsilon q j s l w_q w_j')
qL=sp.Rational(3,2)*O-1; jL=1; sL=1-sp.Rational(9,2)*O; lL=1+3*O+sp.Rational(27,2)*O**2
L={q:qL,j:jL,s:sL,l:lL}
P0=(j-q-2)*l-(3*s+7*j+6*q**2+41*q+22)*s-((3*q+16)*j+20*q**2+64*q+12)*j-(3*q**4+25*q**3+96*q**2+72*q+20)
Q0=(q**2-j*q+2*q)*l+(3*q*s+(4*q+6)*j+6*q**3+44*q**2+22*q-12)*s+(2*j**2+(3*q**2+10*q-6)*j+17*q**3+52*q**2+54*q+36)*j+(3*q**5+28*q**4+118*q**3+72*q**2-76*q-64)
P2=9*s+6*j+9*q**2+66*q+42
Q2=-(6*(q+1)*s+(2*j-2*(1-q))*j+6*q**3+50*q**2+74*q+32)
P3=3*l+3*s-9*(q+4)*j-(45*q**2+78*q+12)
Q3=-(2*(1+q)*l+2*(j+q)*s-(2*j+4*q**2+12*q+6)*j-(30*q**3+84*q**2+78*q+24))
Rs={'printed11.31':(j-q-2)*l-(3*s-2*j+6*q**2+50*q+40)*s+((3*q+10)*j+11*q**2+4*q+18)*j-(3*q**4+34*q**3+246*q+104),
    'upstream33':(j-q-2)*l-(3*s-2*j+6*q**2+50*q+40)*s+((3*q+10)*j+11*q**2+4*q-18)*j-(3*q**4+34*q**3+246*q+104),
    'correct':(j-q-2)*l-(3*s-2*j+6*q**2+50*q+40)*s-((3*q+10)*j+11*q**2+4*q-18)*j-(3*q**4+34*q**3+180*q**2+246*q+104)}
for k,v in Rs.items(): print("R",k,"at LCDM:",sp.factor(v.subs(L)))
print("P0 O+Q0 at LCDM:",sp.factor((P0*O+Q0).subs(L)), " P0,Q0:",sp.factor(P0.subs(L)),sp.factor(Q0.subs(L)))
prD=(3*(9*O+74)*O-556)*O**2+16
print("printedDen:",sp.factor(prD))
pr20=(64-6*O*(9*O+8))/prD/27; pr30=(6*((81*O-110)*O+40)*O+16)/prD/(243*O**2)
print("printed20:",sp.factor(pr20)); print("printed30:",sp.factor(pr30))
# general direction weights (Omega-independent rationals) for (eps_q, eps_j); s,l partials vanish
D0=(P0*O+Q0).subs(L); J0=(j-q-2).subs(L)
g20=lambda x: sp.diff((P2*O+Q2).subs({**L,x:L[x]*(1+e)},simultaneous=True),e).subs(e,0)/(36*D0)
g30=lambda x: sp.diff((P3*O+Q3).subs({**L,x:L[x]*(1+e)},simultaneous=True),e).subs(e,0)/(216*J0*D0)
A20=[sp.factor(g20(x)) for x in (q,j,s,l)]; A30=[sp.factor(g30(x)) for x in (q,j,s,l)]
print("d eta20/d eps_x (x=q,j,s,l):",A20); print("d eta30/d eps_x:",A30)
# Is printed20 = wq*A20q + wj*A20j for constant w? Solve at two Omega values, test at a third.
sol=sp.solve([ (wq*A20[0]+wj*A20[1]-pr20).subs(O,v) for v in (sp.Rational(41,1000),sp.Rational(1,4))],[wq,wj],dict=True)[0]
print("eta20 weights fitting printed at 0.041,0.25:",{k:float(v) for k,v in sol.items()}, " residual at 0.5:", float((sol[wq]*A20[0]+sol[wj]*A20[1]-pr20).subs(O,sp.Rational(1,2))),
      " eta30 with same weights at 0.041,0.25:",[float((sol[wq]*A30[0]+sol[wj]*A30[1]).subs(O,v)) for v in (0.041,0.25)])
sol=sp.solve([ (wq*A30[0]+wj*A30[1]-pr30).subs(O,v) for v in (sp.Rational(41,1000),sp.Rational(1,4))],[wq,wj],dict=True)[0]
print("eta30 weights fitting printed:",{k:float(v) for k,v in sol.items()}, " eta20 with same:",[float((sol[wq]*A20[0]+sol[wj]*A20[1]).subs(O,v)) for v in (0.041,0.25)])
# Wrong-expansion readings: N(eps)=F''-numerator, D(eps)=F-numerator (R cancels)
N2=(P2*O+Q2); N3=(P3*O+Q3)/(j-q-2); Dn=(P0*O+Q0)
fam={q:qL*(1+e),j:jL*(1+e),s:sL*(1+e),l:lL*(1+e)}
N2e=N2.subs(fam,simultaneous=True); N3e=N3.subs(fam,simultaneous=True); De=Dn.subs(fam,simultaneous=True)
d=lambda x,k=1: sp.diff(x,e,k).subs(e,0)
alts={
 "N'/D'(ratio of first-order coeffs)":(d(N2e)/(36*d(De)), d(N3e)/(216*d(De))),
 "N'/(D0+D')":(d(N2e)/(36*(De.subs(e,0)+d(De))), d(N3e)/(216*(De.subs(e,0)+d(De)))),
 "N'/D(eps=1)":(d(N2e)/(36*De.subs(e,1)), d(N3e)/(216*De.subs(e,1))),
 "eta(eps=1) exact":((N2e/(36*De)).subs(e,1),(N3e/(216*De)).subs(e,1)),
 "second-order coeff":(sp.diff(N2e/(36*De),e,2).subs(e,0)/2, sp.diff(N3e/(216*De),e,2).subs(e,0)/2),
}
for k,(a,b) in alts.items():
    a=sp.factor(sp.simplify(a)); b=sp.factor(sp.simplify(b))
    print(k,":",[ (round(float(a.subs(O,v)),4), round(float(b.subs(O,v)),4)) for v in (0.041,0.25)], "match:", sp.simplify(a-pr20)==0, sp.simplify(b-pr30)==0)
# printed vs correct structure
c20=sp.factor(d(N2e/(36*De))); c30=sp.factor(d(N3e/(216*De)))
print("printed20/correct20:",sp.factor(pr20/c20)); print("printed30/correct30:",sp.factor(pr30/c30))
# where (11.42)/(11.43) printed coefficients equal correct: roots in (0,1)
print("agreement roots:", sp.Poly((54*O**2-29*O-2)*(27*O**2+24*O-32),O).nroots())
# radius of validity of the linear approximation: zeros of D(eps) (pole of eta) along the family
for v in (sp.Rational(41,1000),sp.Rational(1,4)):
    p=sp.Poly(sp.expand(De.subs(O,v)),e); r=[complex(x) for x in p.nroots()]
    print("Omega",float(v),"poles of eta in eps (nearest):",sorted(r,key=abs)[:3])
