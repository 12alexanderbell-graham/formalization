from mpmath import mp, mpf, sqrt, log10, log
mp.dps=20
lam=log10(2); xs=[lam/2, 3*lam/2, 5*lam/2]; Z=[sqrt(2),2*sqrt(2),4*sqrt(2)]
def B(a2,a3,x): return x+a2*x**2+a3*x**3
def pw(q): 
    return [z*(1-z**(-q))/q for z in Z] if q!=0 else [z*log(z) for z in Z]
def spread(d,a2,a3,idx=(0,1,2)):
    r=[5*log10(d[i]/B(a2,a3,xs[i])) for i in idx]; return max(r)-min(r)
for q in [mpf(i)/10 for i in range(-20,21)]:
    print(float(q), round(float(spread(pw(q),3.46,1.63)),3), round(float(spread(pw(q),3.46,1.63,(0,2))),3))
