"""C14: eta20, eta30 along the (11.41) common-epsilon family. Emits N1 (numerator / eps) polynomials
and checks the derivative values. P/Q verbatim (11.25)-(11.30)."""
import sympy as sp
q,j,s,l,Om,e=sp.symbols('q j s l Omega epsilon')
P0=(j-q-2)*l-(3*s+7*j+6*q**2+41*q+22)*s-((3*q+16)*j+20*q**2+64*q+12)*j-(3*q**4+25*q**3+96*q**2+72*q+20)
Q0=(q**2-j*q+2*q)*l+(3*q*s+(4*q+6)*j+6*q**3+44*q**2+22*q-12)*s+(2*j**2+(3*q**2+10*q-6)*j+17*q**3+52*q**2+54*q+36)*j+3*q**5+28*q**4+118*q**3+72*q**2-76*q-64
P2=9*s+6*j+9*q**2+66*q+42
Q2=-(6*(q+1)*s+(2*j-2*(1-q))*j+6*q**3+50*q**2+74*q+32)
P3=3*l+3*s-9*(q+4)*j-(45*q**2+78*q+12)
Q3=-(2*(1+q)*l+2*(j+q)*s-(2*j+4*q**2+12*q+6)*j-(30*q**3+84*q**2+78*q+24))
Rc=(j-q-2)*l-(3*s-2*j+6*q**2+50*q+40)*s-((3*q+10)*j+11*q**2+4*q-18)*j-(3*q**4+34*q**3+180*q**2+246*q+104)
L={q:sp.Rational(3,2)*Om-1, j:1, s:1-sp.Rational(9,2)*Om, l:1+3*Om+sp.Rational(27,2)*Om**2}
Le={k:v*(1+e) for k,v in L.items()}
N2=sp.expand((P2*Om+Q2).subs(Le)); N3=sp.expand((P3*Om+Q3).subs(Le))
D=sp.expand((P0*Om+Q0).subs(Le)); J=sp.expand((j-q-2).subs(Le))
assert N2.subs(e,0)==0 and N3.subs(e,0)==0
N2e=sp.expand(sp.cancel(N2/e)); N3e=sp.expand(sp.cancel(N3/e))
print("N2/eps =",N2e); print("N3/eps =",N3e)
print("D(0) =",sp.factor(D.subs(e,0)),"; J(0) =",sp.factor(J.subs(e,0)))
print("Rc at LCDM =",sp.factor(Rc.subs(L)))
c20=sp.factor(N2e.subs(e,0)/(36*D.subs(e,0))); c30=sp.factor(N3e.subs(e,0)/(216*J.subs(e,0)*D.subs(e,0)))
print("correct20 =",c20); print("correct30 =",c30)
pden=(3*(9*Om+74)*Om-556)*Om**2+16
p20=(64-6*Om*(9*Om+8))/pden/27; p30=(6*((81*Om-110)*Om+40)*Om+16)/pden/(243*Om**2)
print("pden =",sp.factor(pden))
print("correct20-printed20 =",sp.factor(c20-p20)); print("correct30-printed30 =",sp.factor(c30-p30))
for o in (sp.Rational(41,1000),sp.Rational(1,4)):
    print(o,[float(x.subs(Om,o)) for x in (c20,p20,c30,p30)])
print("roots in (0,1):",[r for r in sp.Poly((54*Om**2-29*Om-2)*(27*Om**2+24*Om-32)*sp.expand(pden),Om).nroots() if r.is_real and 0<r<1])
# finite-difference check of the derivative directly from the ratio
f20=sp.lambdify((Om,e),N2/(36*D)); f30=sp.lambdify((Om,e),N3/(216*J*D))
for o in (0.041,0.25,0.7):
    h=1e-7; print("fd",o,(f20(o,h)-f20(o,-h))/(2*h),float(c20.subs(Om,o)),(f30(o,h)-f30(o,-h))/(2*h),float(c30.subs(Om,o)))
def lean(x): return str(x).replace('**','^').replace('Omega','Ω').replace('epsilon','ε')
open('N.txt','w').write("N2e: "+lean(N2e)+"\nN3e: "+lean(N3e)+"\n")
