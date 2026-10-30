"""Referee: check the multiplied-out identities of fR_values are polynomial consequences of the
referee's own (series-derived) equations E1, E2, dE2 — i.e. hold with no nondegeneracy hypothesis.
Coefficients c_k found by the referee via adj(M) reasoning are checked here as exact identities."""
import sympy as sp, pickle
q,j,s,l,Om,H0=sp.symbols('q0 j0 s0 l0 Omega H0',real=True)
f0,f2,f3,Fp=sp.symbols('f0 f2 f3 Fp')
d=pickle.load(open('/tmp/claude-0/referee/eqs.pkl','rb'))
E1,E2,E3=[sp.expand(e.subs(Fp,1)) for e in d['eqs']]
P0=(j-q-2)*l-(3*s+7*j+6*q**2+41*q+22)*s-((3*q+16)*j+20*q**2+64*q+12)*j-(3*q**4+25*q**3+96*q**2+72*q+20)
Q0=(q**2-j*q+2*q)*l+(3*q*s+(4*q+6)*j+6*q**3+44*q**2+22*q-12)*s+(2*j**2+(3*q**2+10*q-6)*j+17*q**3+52*q**2+54*q+36)*j+(3*q**5+28*q**4+118*q**3+72*q**2-76*q-64)
P2=9*s+6*j+9*q**2+66*q+42
Q2=-(6*(q+1)*s+(2*j-2*(1-q))*j+6*q**3+50*q**2+74*q+32)
P3=3*l+3*s-9*(q+4)*j-(45*q**2+78*q+12)
Q3=-(2*(1+q)*l+2*(j+q)*s-(2*j+4*q**2+12*q+6)*j-(30*q**3+84*q**2+78*q+24))
Rco=(j-q-2)*l-(3*s-2*j+6*q**2+50*q+40)*s-((3*q+10)*j+11*q**2+4*q-18)*j-(3*q**4+34*q**3+180*q**2+246*q+104)
T0=Rco*f0+6*H0**2*(P0*Om+Q0)
T2=Rco*6*H0**2*f2+(P2*Om+Q2)
T3=(j-q-2)*Rco*36*H0**4*f3+(P3*Om+Q3)
# general ansatz: c_k polynomial in (q,j,s,l) of degree<=2 times H0^{-n}; solve the linear system
import itertools
mons=[q**a*j**b*s**c*l**dd for a,b,c,dd in itertools.product(range(3),repeat=4) if a+b+c+dd<=2]
for nm,T in (('T0',T0),('T2',T2),('T3',T3)):
    found=False
    for n1,n2,n3 in ((0,0,1),(0,2,3),(2,2,3),(0,1,2),(1,2,3)):
        cs=[sp.symbols(f'c{k}_0:{len(mons)}') for k in range(3)]
        C=[sum(ci*m for ci,m in zip(cs[k],mons)) for k in range(3)]
        expr=sp.expand(T*H0**3-(C[0]*E1*H0**(3-n1)+C[1]*E2*H0**(3-n2)+C[2]*E3*H0**(3-n3)))
        eqs=sp.Poly(expr,q,j,s,l,Om,H0,f0,f2,f3).coeffs()
        sol=sp.solve(eqs,[x for c in cs for x in c],dict=True)
        if sol:
            Cs=[sp.factor(C[k].subs(sol[0]).subs({x:0 for c in cs for x in c})) for k in range(3)]
            res=sp.expand(T*H0**3-(Cs[0]*E1*H0**(3-n1)+Cs[1]*E2*H0**(3-n2)+Cs[2]*E3*H0**(3-n3)))
            print(nm,": T*H0^3 = c1*H0^%d*E1 + c2*H0^%d*E2 + c3*H0^%d*E3 with"%(3-n1,3-n2,3-n3),Cs,"; residual",res)
            found=True; break
    if not found: print(nm,": no certificate in ansatz")
# T0: c1 = 2*Rco (E1 is linear in f0 with coefficient -1/2), remaining f2,f3 eliminated by E2,E3
c1=-2*Rco      # E1 has f0 with coefficient -1/2
c2=-6*(-j+q+2)*(-j+3*q**2+25*q+3*s+20)
c3=-6*(-j+q+2)**2/H0
res=sp.expand(T0-(c1*E1+c2*E2+c3*E3))
print("T0 = -2Rco*E1 - 6(q+2-j)(3q^2+25q+3s+20-j)*E2 - 6(q+2-j)^2/H0*E3 ; residual",res)
