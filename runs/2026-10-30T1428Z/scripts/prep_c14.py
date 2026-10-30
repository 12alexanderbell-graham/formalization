"""Prep for C14 (next run): eta20 = F''(R0) H0^4 / F(R0) = (P2 Om + Q2)/(36 (P0 Om + Q0)) and
eta30 = F'''(R0) H0^6 / F(R0) = (P3 Om + Q3)/(216 (j-q-2)(P0 Om + Q0)) (from fR_values; R cancels).
With (q,j,s,l) = LCDM values * (1+eps): d/deps at 0, vs printed (11.42)-(11.43)."""
import sympy as sp
exec(open('cert.py').read().split("c1,c2,c3=")[0].replace("print(","(lambda *a,**k:None)("))
eps=sp.symbols('epsilon')
L={q:sp.Rational(3,2)*Om-1, j:1, s:1-sp.Rational(9,2)*Om, l:1+3*Om+sp.Rational(27,2)*Om**2}
Le={k:v*(1+eps) for k,v in L.items()}
e20=(P2*Om+Q2)/(36*(P0*Om+Q0)); e30=(P3*Om+Q3)/(216*(j-q-2)*(P0*Om+Q0))
d20=sp.factor(sp.diff(e20.subs(Le),eps).subs(eps,0)); d30=sp.factor(sp.diff(e30.subs(Le),eps).subs(eps,0))
print("eta20 at eps=0:",sp.simplify(e20.subs(L)),"; d/deps:",d20)
print("eta30 at eps=0:",sp.simplify(e30.subs(L)),"; d/deps:",d30)
D_=(3*(9*Om+74)*Om-556)*Om**2+16
p20=(64-6*Om*(9*Om+8))/D_/27; p30=(6*((81*Om-110)*Om+40)*Om+16)/D_/(243*Om**2)
for o in (sp.Rational(41,1000),sp.Rational(1,4)):
    print(o, float(d20.subs(Om,o)), float(p20.subs(Om,o)), float(d30.subs(Om,o)), float(p30.subs(Om,o)))
print("P2 Om+Q2, P3 Om+Q3 at LCDM:",sp.expand((P2*Om+Q2).subs(L)),sp.expand((P3*Om+Q3).subs(L)))
