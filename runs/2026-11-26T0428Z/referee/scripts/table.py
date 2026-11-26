import mpmath as M, sys
M.mp.dps=50
def load(f):
    r=[]
    for line in open(f):
        p=line.split(); r.append((M.mpf(p[3]),M.mpf(p[5]),M.mpf(p[7])))
    return r
A=load('out25.txt'); B=load('out45.txt')
print('max rel diff xi (dps25 vs 45):',M.nstr(max(abs(a[0]/b[0]-1) for a,b in zip(A,B)),3),
      ' max rel diff (m-c):',M.nstr(max(abs(a[1]/b[1]-1) for a,b in zip(A,B)),3))
L0=M.exp(2*M.pi/M.sqrt(7)); q0=-M.exp(-M.pi/M.sqrt(7))
print('exp(2pi/sqrt7)=',M.nstr(L0,15),' -exp(-pi/sqrt7)=',M.nstr(q0,15))
for n in range(0,8):
    a,b=B[n+5],B[n+6]
    d1=abs(b[0]/a[0]-L0); d2=abs(b[1]/a[1]-q0)
    B1=M.mpf(23)/10*(M.mpf(21)/50)**n; B2=M.mpf(3)/20*(M.mpf(21)/50)**n
    e=a[2]
    print(f"n={n} ratio={M.nstr(b[0]/a[0],12)} d1={M.nstr(d1,6)} d1/B1={M.nstr(d1/B1,4)} d1/eps={M.nstr(d1/e,4)} | q={M.nstr(b[1]/a[1],12)} d2={M.nstr(d2,6)} d2/B2={M.nstr(d2/B2,4)} d2/eps={M.nstr(d2/e,4)} | eps={M.nstr(e,5)} eps/(0.0057*0.42^n)={M.nstr(e/(M.mpf('0.0057')*M.mpf('0.42')**n),4)} epsratio={M.nstr(b[2]/a[2],5)}")
