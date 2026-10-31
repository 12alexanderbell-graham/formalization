from sympy import *
import pickle
Om,w0,wa=symbols('Omega w0 wa')
c=pickle.load(open('cpl.pkl','rb'))
q=-c[2]; 
claims={
2:-(Rational(1,2)+Rational(3,2)*(1-Om)*w0),
3:1+Rational(3,2)*(1-Om)*(3*w0*(1+w0)+wa),
4:-Rational(7,2)-Rational(33,4)*(1-Om)*wa-Rational(9,4)*(1-Om)*(9+(7-Om)*wa)*w0-Rational(9,4)*(1-Om)*(16-3*Om)*w0**2-Rational(27,4)*(1-Om)*(3-Om)*w0**3,
5:Rational(35,2)+(1-Om)/4*(213+9*(7-Om)*wa)*wa+(1-Om)/4*(489+9*(82-21*Om)*wa)*w0+Rational(9,2)*(1-Om)*(67-21*Om+Rational(3,2)*(23-11*Om)*wa)*w0**2+Rational(27,4)*(1-Om)*(47-24*Om)*w0**3+Rational(81,2)*(1-Om)*(3-2*Om)*w0**4}
print(simplify(q-claims[2]*(-1)*(-1)) if False else simplify(-c[2]-claims[2]))  # decel = -coeff2
for n in (3,4,5):
    print(n, expand(c[n]-claims[n]))
# toy
vals={Om:Rational(245,1000),w0:Rational(-93,100),wa:Rational(-41,100)}
print(N(c[5].subs(vals)),N(claims[5].subs(vals)))
