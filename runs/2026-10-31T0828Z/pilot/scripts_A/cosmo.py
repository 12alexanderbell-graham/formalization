from sympy import *
z,Om,w0,wa=symbols('z Omega w0 wa')
def coeffs(H2,N=6):
    H=sqrt(H2)
    C=[Integer(1)]
    for n in range(N):
        c=C[-1]
        C.append(H*c-(1+z)*H*diff(c,z))
    out=[]
    for n in range(N+1):
        out.append(simplify((C[n]/H**n).subs(z,0)))
    return out
if __name__=="__main__":
    E1=Om*(1+z)**3+1-Om
    c=coeffs(E1)
    for n,v in enumerate(c): print(n,factor(v), expand(v))
    E2=Om*(1+z)**3+(1-Om)*(1+z)**(3*(1+w0+wa))*exp(-3*wa*z/(1+z))
    c2=coeffs(E2,5)
    import pickle
    pickle.dump(c2,open('cpl.pkl','wb'))
    for n,v in enumerate(c2): print(n,expand(v))
