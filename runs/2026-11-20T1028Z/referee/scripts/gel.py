import mpmath as mp, sys
mp.mp.dps=40
# series W = sum a_k s^{2k}: W''+2W'/s = -e^W. Use power series via recurrence on e^W.
N=40
def series(N):
    a=[mp.mpf(0)]*(N+1); e=[mp.mpf(0)]*(N+1); e[0]=mp.mpf(1)
    # W=sum a_k x^k, x=s^2 ; Laplacian s^{2k-2}*2k(2k+1) a_k => coefficient of x^{k-1}: 2k(2k+1)a_k = -e_{k-1}
    # e=exp(W): k e_k = sum_{j=1..k} j a_j e_{k-j}
    for k in range(1,N+1):
        a[k]=-e[k-1]/(2*k*(2*k+1))
        e[k]=sum(j*a[j]*e[k-j] for j in range(1,k+1))/k
    return a
a=series(N)
s0=mp.mpf('0.5')
W0=sum(a[k]*s0**(2*k) for k in range(N+1))
dW0=sum(2*k*a[k]*s0**(2*k-1) for k in range(1,N+1))
def run(s0,W0,dW0,ends,tol):
    # integrate (W,W') in s with mp.odefun (Taylor)
    f=mp.odefun(lambda s,y:[y[1],-2*y[1]/s-mp.exp(y[0])],s0,[W0,dW0],tol=tol,degree=30)
    return f
def analyse(tol):
    f=run(s0,W0,dW0,None,tol)
    lam=lambda s: s**2*mp.exp(f(s)[0])
    g=lambda s: 2+s*f(s)[1]
    # scan for zeros of g
    zs=[]; prev=g(mp.mpf(1)); s=mp.mpf(1); ds=mp.mpf('0.25')
    while s<5000 and len(zs)<4:
        # log-step
        s2=s*mp.mpf('1.02') if s>10 else s+ds
        cur=g(s2)
        if prev*cur<0:
            z=mp.findroot(g,(s,s2),solver='anderson',tol=mp.mpf(10)**-25)
            zs.append(z)
        prev=cur; s=s2
    return f,zs,lam
if __name__=="__main__":
    tol=mp.mpf(10)**-int(sys.argv[1])
    f,zs,lam=analyse(tol)
    for z in zs: print(mp.nstr(z,20),mp.nstr(lam(z),20))
    # u,v checks
    uv=lambda s:(s*mp.exp(f(s)[0])/(-f(s)[1]), -s*f(s)[1])
    us=[]; 
    for i in range(0,3201):
        s=mp.mpf(4380)+mp.mpf(i)/10
        if s>4700: break
        us.append((s,)+uv(s))
    print('u min/max on [4380,4700]',mp.nstr(min(x[1] for x in us),10),mp.nstr(max(x[1] for x in us),10))
    print('v(4380)',mp.nstr(uv(4380)[1],10),'v(4700)',mp.nstr(uv(4700)[1],10))
    vs=[uv(mp.mpf(428.95)+ (4380-mp.mpf(428.95))*i/400)[1] for i in range(401)]
    print('min v on [428.95,4380]',mp.nstr(min(vs),10))
