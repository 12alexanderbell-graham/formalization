from sympy import *
import pickle
q,j,s,l,Om,x=symbols('q j s l Omega x')
CL,CA=pickle.load(open('bamba_y.pkl','rb'))
D=lambda C,n: C[n]   # C[n] is coeff of y^(n+1)? CL list index n = coefficient of y^{n+1}; D^n coefficient is y^{n+1} -> index n
pD2=-Rational(1,6)*(12-5*q+3*q**2-j-Om)
pD3=Rational(1,24)*(52-20*q+21*q**2-15*q**3-7*j+10*q*j+s-2*Om*(1+3*q))
pD4=Rational(1,120)*(359-184*q+186*q**2-135*q**3+105*q**4+90*q*j-105*q**2*j-15*q*s-57*j+10*j**2+9*s-l-5*Om*(17-6*q+9*q**2-2*j))
cD3=pD3+(Om-1)*(3*q-2)/6
print('D2+printed', simplify(CL[2]+pD2))
print('D3 correct diff', simplify(CL[3]-cD3))
print('D3 printed diff', factor(CL[3]-pD3))
d4=expand(CL[4]-pD4)
print('D4 diff', factor(d4)); print(expand(d4.subs(Om,x+1)))
print('expected', expand(Rational(1,120)*x**2+Rational(5,12)*q*x))
pA1=-Rational(1,2)*(1+q); pA2=-Rational(1,6)*(-q-3*q**2+j+Om)
pA3=-Rational(1,24)*(-2*q+3*q**2+15*q**3-j-10*q*j-s+2*Om)
pA4=-Rational(1,120)*(1-6*q+9*q**2-15*q**3-105*q**4+10*q*j+105*q**2*j+15*q*s-3*j-10*j**2+s+l+5*Om)
print('DA1',simplify(CA[1]-pA1))
print('DA2',simplify(CA[2]-pA2))
print('DA3',factor(simplify(CA[3]-pA3)))
print('DA3 corr',simplify(CA[3]-(pA3+q*(Om-1)/4)))
d=expand(CA[4]-pA4); print('DA4',factor(d)); print(expand(d.subs(Om,x+1)))
