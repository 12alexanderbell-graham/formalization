import sys, mpmath as M
dps=int(sys.argv[1]); M.mp.dps=dps
coef=[M.mpf(-1)/6,M.mpf(1)/120,M.mpf(-1)/1890,M.mpf(61)/1632960,M.mpf(-629)/224532000,M.mpf(2869)/13135122000]
s0=M.mpf('1e-4')
w=sum(c*s0**(2*i+2) for i,c in enumerate(coef)); wp=sum((2*i+2)*c*s0**(2*i+1) for i,c in enumerate(coef))
u0=s0*M.exp(w)/(-wp); v0=-s0*wp
t0=M.log(s0)
F=M.odefun(lambda t,y:[y[0]*(3-y[0]-y[1]), y[1]*(y[0]-1)], t0,[u0,v0])
g=lambda t:(lambda y:2*y[0]-y[1])(F(t))
zs=[]; t=t0; h=M.mpf('0.02'); gp=g(t)
while len(zs)<14:
    t2=t+h; g2=g(t2)
    if gp*g2<0: zs.append(M.findroot(g,(t,t2),solver='anderson'))
    t,gp=t2,g2
c=M.sqrt(2/M.pi); L0=2*M.pi/M.sqrt(7); q0=-M.exp(-M.pi/M.sqrt(7))
for k,tk in enumerate(zs):
    u,v=F(tk); m=M.sqrt(u*v**3/(4*M.pi)); Nw=7*(u-1)**2+(u-1+2*(v-2))**2
    print('k',k,'xi',M.nstr(M.exp(tk),25),'m-c',M.nstr(m-c,25),'eps',M.nstr(M.sqrt(Nw),15))
