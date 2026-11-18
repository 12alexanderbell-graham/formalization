from mpmath import mp, mpf, sqrt, log10, log
mp.dps=20
lam=log10(2); xs=[lam/2, 3*lam/2, 5*lam/2]; L10=log(10); k=mpf(20)/3*lam
rho=mpf(2)**(mpf(1)/4)
EdS=[3*(rho**2-rho), 6*(rho**2-1/rho), 12*rho**2-6*rho]
Z=[sqrt(2),2*sqrt(2),4*sqrt(2)]; dS=[z*(z-1) for z in Z]
def B(a2,a3,x): return x+a2*x**2+a3*x**3
def A2(O): return L10*(mpf(3)/2-mpf(3)/4*O)
def A3(O): return L10**2*(mpf(9)/8*O**2-2*O+mpf(7)/6)
def viol(O,a2,a3): return a2-A2(O)+mpf(1)/2 - k*(a3-A3(O))
def spread(d,a2,a3,sgn=1):
    r=[]
    for i in range(3):
        b=B(a2,a3,xs[i])*sgn
        if b==0: return None
        r.append(5*log10(abs(d[i]/b)))
    return max(r)-min(r)
# rl19 single-bound drops
for name,d in [('EdS',EdS),('dS',dS)]:
  for lab,rng2,rng3 in [('a2<3.43',[mpf(i)/100 for i in range(-500,343,3)],[mpf(i)/100 for i in range(157,170)]),
                       ('a2>3.49',[mpf(i)/100 for i in range(350,3000,10)],[mpf(i)/100 for i in range(157,170)]),
                       ('a3<1.57',[mpf(i)/100 for i in range(343,350)],[mpf(i)/100 for i in range(-1000,157,5)]),
                       ('a3>1.69',[mpf(i)/100 for i in range(343,350)],[mpf(i)/100 for i in range(170,2000,5)])]:
    best=min((spread(d,a2,a3),a2,a3) for a2 in rng2 for a3 in rng3 if min(B(a2,a3,x) for x in xs)>0)
    print(name,lab,[float(v) for v in best])
# fit_direction: H<0 (B<0 all), drops of hp_i (B_i<=0)
for name,d,O in [('EdS',EdS,1),('dS',dS,0)]:
  g=[(mpf(i)/4,mpf(j)/4) for i in range(-200,200) for j in range(-200,200)]
  c=[(spread(d,a2,a3,-1),a2,a3) for a2,a3 in g if max(B(a2,a3,x) for x in xs)<0 and viol(O,a2,a3)>0.3]
  print(name,'H<0',[float(v) for v in min(c)] if c else None)
  for i in range(3):
    c=[]
    for a2,a3 in g:
      Bs=[B(a2,a3,x) for x in xs]
      if Bs[i]>=0 or min(Bs[j] for j in range(3) if j!=i)<=0: continue
      if viol(O,a2,a3)<=0.3: continue
      c.append((spread(d,a2,a3),a2,a3))
    print(name,'hp',i+1,'negative',[float(v) for v in min(c)] if c else None)
