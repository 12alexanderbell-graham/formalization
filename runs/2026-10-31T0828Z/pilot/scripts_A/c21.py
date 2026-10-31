from sympy import *
y,Om=symbols('y Omega')
zz=symbols('zz')
E=sqrt(Om*(1+zz)**3+1-Om)
ser=series(1/E,zz,0,5).removeO()
I=integrate(ser,zz)
dl=(1+zz)*I
# substitute zz=exp(y)-1
d=series(dl.subs(zz,exp(y)-1),y,0,5).removeO()
print([factor(d.coeff(y,k)) for k in range(1,5)])
