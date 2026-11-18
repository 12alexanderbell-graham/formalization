from mpmath import mp, quad, sqrt, log10, sin, sinh
mp.dps=20
def P(z,c):
    x=log10(1+z); a2,a3,a4=c; return x+a2*x**2+a3*x**3+a4*x**4
z3=2*sqrt(2)-1; z5=4*sqrt(2)-1
def D(Om,O0,c):
    E=lambda z: sqrt(Om*(1+z)**3+(1-O0)*(1+z)**2+O0-Om)
    def d(z):
        chi=quad(lambda u:1/E(u),[0,z]); k=1-O0
        if k<0: S=sin(sqrt(-k)*chi)/sqrt(-k)
        elif k>0: S=sinh(sqrt(k)*chi)/sqrt(k)
        else: S=chi
        return (1+z)*S
    return 5*log10((d(z5)/P(z5,c))/(d(z3)/P(z3,c)))
cs=(3.075,4.466,-3.716); cg=(3.205,3.564,-2.510)
import sys
for Om,O0 in [(0.3,1),(0.1,1),(0,1),(0,1.1),(-0.01,1),(1,1),(1,1.1),(10,1),(100,1),(1000,1),(0.3,1.5),(0.3,2),(0.3,3),(1,2),(0.5,3),(0.3,0.9),(0.3,0.5),(0.3,0.3),(0.1,0.1),(1,0.5),(0.3,-1)]:
    try: print(Om,O0, D(Om,O0,cs), D(Om,O0,cg))
    except Exception as e: print(Om,O0,'err',e)
