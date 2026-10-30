import sympy as sp
exec(open('derive_fr.py').read().split("sol=sp.solve")[0])
P0=(j-q-2)*l-(3*s+7*j+6*q**2+41*q+22)*s-((3*q+16)*j+20*q**2+64*q+12)*j-(3*q**4+25*q**3+96*q**2+72*q+20)
Q0=(q**2-j*q+2*q)*l+(3*q*s+(4*q+6)*j+6*q**3+44*q**2+22*q-12)*s+(2*j**2+(3*q**2+10*q-6)*j+17*q**3+52*q**2+54*q+36)*j+3*q**5+28*q**4+118*q**3+72*q**2-76*q-64
P2=9*s+6*j+9*q**2+66*q+42
Q2=-(6*(q+1)*s+(2*j-2*(1-q))*j+6*q**3+50*q**2+74*q+32)
P3=3*l+3*s-9*(q+4)*j-(45*q**2+78*q+12)
Q3=-(2*(1+q)*l+2*(j+q)*s-(2*j+4*q**2+12*q+6)*j-(30*q**3+84*q**2+78*q+24))
Rc=(j-q-2)*l-(3*s-2*j+6*q**2+50*q+40)*s-((3*q+10)*j+11*q**2+4*q-18)*j-(3*q**4+34*q**3+180*q**2+246*q+104)
c1,c2,c3=sp.symbols('c1 c2 c3')
T0=Rc*x0+6*H0**2*(P0*Om+Q0)
T2=Rc*x2*6*H0**2+(P2*Om+Q2)
T3=(j-q-2)*Rc*x3*36*H0**4+(P3*Om+Q3)
for nm,T in (('T0',T0),('T2',T2),('T3',T3)):
    for mult in (1,H0,H0**2,H0**3,H0**4,H0**5,H0**6):
        expr=sp.expand(mult*T-(c1*E1+c2*E2+c3*E3))
        eqs=[sp.expand(expr.coeff(v)) for v in (x0,x2,x3)]+[sp.expand(expr.subs({x0:0,x2:0,x3:0}))]
        sol=sp.solve(eqs,[c1,c2,c3],dict=True)
        if sol:
            cs=[sp.factor(sol[0][c]) for c in (c1,c2,c3)]
            print(nm,"mult",mult,":",cs)
            break
    else: print(nm,"no cert")
