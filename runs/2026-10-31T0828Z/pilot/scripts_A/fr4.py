from sympy import *
import pickle
from fr import *
q,j,s,l,Om=symbols('q j s l Omega')
t=symbols('t')
F0s,F2s,F3s,R0=pickle.load(open('fsol.pkl','rb'))
e20=(P2(q,j,s)*Om+Q2(q,j,s))/(36*(P0(q,j,s,l)*Om+Q0(q,j,s,l)))
e30=(P3(q,j,s,l)*Om+Q3(q,j,s,l))/(216*(j-q-2)*(P0(q,j,s,l)*Om+Q0(q,j,s,l)))
import random
for _ in range(3):
    v={q:Rational(random.randint(-9,9),7),j:Rational(random.randint(-9,9),5),s:Rational(random.randint(-9,9),3),l:Rational(random.randint(-9,9),4),Om:Rational(random.randint(1,9),10)}
    print(N((F2s/F0s).subs(v)),N(e20.subs(v)),N((F3s/F0s).subs(v)),N(e30.subs(v)))
Rtrue=factor(simplify(-6*(P0(q,j,s,l)*Om+Q0(q,j,s,l))/F0s))
print(Rtrue)
print(factor(simplify(Rtrue-printedR(q,j,s,l))))
