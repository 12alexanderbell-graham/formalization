from mpmath import *
mp.dps=30
def ex(Om,z):
    return (1+z)*quad(lambda s:1/sqrt(Om*(1+s)**3+1-Om),[0,z])
def poly(Om,z):
    L=log(10); x=log10(1+z)
    a2=L*(mpf(3)/2-mpf(3)/4*Om); a3=L**2*(mpf(9)/8*Om**2-2*Om+mpf(7)/6)
    return L*(x+a2*x**2+a3*x**3)
for z in (3,7):
    for Om in [0.2,0.25,0.3,0.35,0.4]:
        print(z,Om,poly(Om,z),ex(Om,z),5*log10(ex(Om,z)/poly(Om,z)) if poly(Om,z)>0 else None)
print('----')
for z in (3,7):
    vals=[]
    for i in range(0,201):
        Om=mpf(0.2)+mpf(0.2)*i/200
        vals.append((5*log10(ex(Om,z)/poly(Om,z)),Om))
    print(z,min(vals),max(vals))
