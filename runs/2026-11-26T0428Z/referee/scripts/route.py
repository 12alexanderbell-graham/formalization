from mpmath import iv, mpf
iv.dps=30
PI=iv.mpf(['3.141592','3.141593']); R7=iv.mpf(['2.64575','2.6458'])
E=iv.mpf('0.0057')  # worst case eps (all coefficient functions below are increasing in eps)
L0=2*PI/R7
Lmin=PI/(R7/2+16*E); Lmax=PI/(R7/2-16*E)
print('L0',L0,' Lmin',Lmin,' Lmax',Lmax)
# (a)
a=-(1-36*E)*Lmin/2
print('(a) exponent upper bound',a.b,' exp',iv.exp(a).b,' <= 0.42 ?',iv.exp(a).b<=mpf('0.42'))
# (b)
dL=iv.mpf([max((Lmax-L0).b,(L0-Lmin).b)]*2)
print('(b) |L-L0|/eps <=',(dL/E).b,' (need 31)')
deL=max((iv.exp(Lmax)-iv.exp(L0)).b,(iv.exp(L0)-iv.exp(Lmin)).b)
print('    |e^L-e^L0|/eps <=',deL/E.a,' (need 400)  via 31eps:',(iv.exp(L0+31*E)-iv.exp(L0)).b/E.a)
# (c)
q0=iv.exp(-PI/R7)
dp=(L0/2-(1-36*E)*Lmin/2)   # D/2 - (-L0/2) max
dm=((1+36*E)*Lmax/2-L0/2)   # -(D/2 + L0/2) max
print('    half-advance deviation /eps: up',dp.b/E.a,' down',dm.b/E.a,' (doc says 62)')
Rmax=(2+E/5)/(2-E/5); Rmin=(2-E/5)/(2+E/5)
up=q0*(iv.exp(dp)*Rmax-1); dn=q0*(1-iv.exp(-dm)*Rmin)
print('(c) |Q+e^{-pi/sqrt7}|/eps <=',max(up.b,dn.b)/E.a,' (need 26)')
# crude version: 62eps deviation via mean value
crude=q0*(iv.exp(62*E)-1)*Rmax+q0*(Rmax-1)
print('    crude via 62eps:',crude.b/E.a)
print('    |u-1|<=eps/sqrt32, 1/sqrt32=',1/iv.sqrt(32))
# (d)
print('(d) 400*0.0057=',400*mpf('0.0057'),'<=2.3 ; 26*0.0057=',26*mpf('0.0057'),'<=0.15')
print('base: sqrt(3234e-8)=',iv.sqrt(iv.mpf('3234e-8')).b,'<=0.0057')
print('--- sensitivity of (c) to how exp difference is bounded ---')
mv=q0*iv.exp(62*E)*62*E*Rmax + q0*(Rmax-1)
print('MVT with e^{-L0/2+62eps}*62eps:',mv.b/E.a)
mv2=max((q0*iv.exp(dp)*dp*Rmax+q0*(Rmax-1)).b,(q0*dm+q0*(1-Rmin)).b)
print('MVT one-sided (53.43 up / 61.34 down):',mv2/E.a)
print('MVT for (b) with 31eps: e^{L0+31eps}*31 =',(iv.exp(L0+31*E)*31).b)
