from sympy import *
z,Om=symbols('z Omega')
E=sqrt(Om*(1+z)**3+1-Om)
def D(f): return -(1+z)*E*diff(f,z)
a=1/(1+z)
def coeff(n,E):
    f=a
    for i in range(n): f=-(1+z)*E*diff(f,z)
    return simplify((f/(a*E**n)).subs(z,0))
for n in [2,3,4,5,6]:
    print(n, factor(expand(simplify(coeff(n,E)))), expand(simplify(coeff(n,E))))
