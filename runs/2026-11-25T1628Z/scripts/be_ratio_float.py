import mpmath as mp
mp.mp.dps=30
# solve in t=log s with w, phi series start
def f(t,Y):
    u,v=Y
    return [u*(3-u-v), v*(u-1)]
s0=mp.mpf('1e-4'); 
w=-s0**2/6+s0**4/120; ph=-s0/3+s0**3/30
u=s0*mp.e**w/(-ph); v=-s0*ph
t0=mp.log(s0)
sol=mp.odefun(f,t0,[u,v])
c=mp.sqrt(2/mp.pi)
def g(t):
    u,v=sol(t); return 2*u-v
def m(t):
    u,v=sol(t); return mp.sqrt(u*v**3/(4*mp.pi))
# scan
t=mp.mpf(0); prev=g(t); roots=[]
h=mp.mpf('0.05')
while t<40:
    t2=t+h; gv=g(t2)
    if prev*gv<0:
        roots.append(mp.findroot(g,(t,t2),solver='anderson'))
    t,prev=t2,gv
xi=[mp.e**r for r in roots]
print('xi0',xi[0])
for k in range(len(roots)-1):
    print(k, mp.nstr(xi[k],12), mp.nstr(xi[k+1]/xi[k],8), mp.nstr((m(roots[k+1])-c)/(m(roots[k])-c),8))
print('targets',mp.e**(2*mp.pi/mp.sqrt(7)), -mp.e**(-mp.pi/mp.sqrt(7)))
