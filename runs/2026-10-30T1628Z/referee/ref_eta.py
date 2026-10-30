# Referee fresh derivation for C14 (eta20, eta30 along (11.41)).
import sympy as sp
O,e,q,j,s,l = sp.symbols('Omega epsilon q j s l')
P0=(j-q-2)*l-(3*s+7*j+6*q**2+41*q+22)*s-((3*q+16)*j+20*q**2+64*q+12)*j-(3*q**4+25*q**3+96*q**2+72*q+20)
Q0=(q**2-j*q+2*q)*l+(3*q*s+(4*q+6)*j+6*q**3+44*q**2+22*q-12)*s+(2*j**2+(3*q**2+10*q-6)*j+17*q**3+52*q**2+54*q+36)*j+(3*q**5+28*q**4+118*q**3+72*q**2-76*q-64)
P2=9*s+6*j+9*q**2+66*q+42
Q2=-(6*(q+1)*s+(2*j-2*(1-q))*j+6*q**3+50*q**2+74*q+32)
P3=3*l+3*s-9*(q+4)*j-(45*q**2+78*q+12)
Q3=-(2*(1+q)*l+2*(j+q)*s-(2*j+4*q**2+12*q+6)*j-(30*q**3+84*q**2+78*q+24))
Rp=(j-q-2)*l-(3*s-2*j+6*q**2+50*q+40)*s+((3*q+10)*j+11*q**2+4*q+18)*j-(3*q**4+34*q**3+246*q+104)
Rc=(j-q-2)*l-(3*s-2*j+6*q**2+50*q+40)*s-((3*q+10)*j+11*q**2+4*q-18)*j-(3*q**4+34*q**3+180*q**2+246*q+104)
qL=sp.Rational(3,2)*O-1; jL=1; sL=1-sp.Rational(9,2)*O; lL=1+3*O+sp.Rational(27,2)*O**2
def fam(ex, eq=e, ej=e, es=e, el=e):
    return ex.subs({q:qL*(1+eq),j:jL*(1+ej),s:sL*(1+es),l:lL*(1+el)},simultaneous=True)
F  = -(P0*O+Q0)            # F/(6H^2) * R   (R cancels)
F2 = -(P2*O+Q2)            # F''*6H^2 * R
F3 = -(P3*O+Q3)/(j-q-2)    # F'''*36H^4 * R
eta20 = (F2/36)/F          # F'' H^4 / F
eta30 = (F3/216)/F
print("LCDM checks:", sp.simplify(fam(P2*O+Q2).subs(e,0)), sp.simplify(fam(P3*O+Q3).subs(e,0)),
      sp.factor(fam(P0*O+Q0).subs(e,0)), sp.factor(fam(Rc).subs(e,0)), sp.factor(fam(Rp).subs(e,0)), sp.factor(fam(j-q-2).subs(e,0)))
c20 = sp.factor(sp.diff(fam(eta20),e).subs(e,0)); c30=sp.factor(sp.diff(fam(eta30),e).subs(e,0))
print("c20 =",c20); print("c30 =",c30)
prD=(3*(9*O+74)*O-556)*O**2+16
pr20=(64-6*O*(9*O+8))/prD/27; pr30=(6*((81*O-110)*O+40)*O+16)/prD/(243*O**2)
cor20=-2*(27*O**2+24*O-32)/(27*O*(O-2)*(27*O**2+60*O+112))
cor30=-2*(81*O**2-60*O-16)/(243*O**2*(O-2)*(27*O**2+60*O+112))
print("match program:", sp.simplify(c20-cor20), sp.simplify(c30-cor30))
for w in [sp.Rational(41,1000), sp.Rational(1,4)]:
    print(float(w), "correct", float(c20.subs(O,w)), float(c30.subs(O,w)), "printed", float(pr20.subs(O,w)), float(pr30.subs(O,w)))
print("roots printedDen:", [r for r in sp.Poly(prD,O).nroots() ])
print("c20-pr20 num:", sp.factor(sp.together(c20-pr20)))
print("c30-pr30 num:", sp.factor(sp.together(c30-pr30)))
# finite-difference check on the exact ratio
for w in [0.041,0.25]:
    f20=sp.lambdify(e,fam(eta20).subs(O,sp.nsimplify(w)),'mpmath'); f30=sp.lambdify(e,fam(eta30).subs(O,sp.nsimplify(w)),'mpmath')
    import mpmath; mpmath.mp.dps=40
    h=mpmath.mpf('1e-12')
    print(w,"FD", (f20(h)-f20(-h))/(2*h), (f30(h)-f30(-h))/(2*h), "at eps=0.1:", f20(mpmath.mpf('0.1')), f30(mpmath.mpf('0.1')),"eps=-0.1:",f20(mpmath.mpf('-0.1')), f30(mpmath.mpf('-0.1')))
