import mpmath as mp, pickle, sympy as sp
mp.mp.dps=40
Om=mp.mpf('0.3'); OL=1-Om
a=lambda t: (Om/OL)**(mp.mpf(1)/3)*mp.sinh(mp.mpf(3)/2*mp.sqrt(OL)*t)**(mp.mpf(2)/3)   # H0=1 units
t0=mp.findroot(lambda t:a(t)-1,1)
d=[mp.diff(a,t0,n) for n in range(6)]
H=d[1]; q=-d[2]/H**2; j=d[3]/H**3; s=d[4]/H**4; l=d[5]/H**5
print("H0=",mp.nstr(H,15)," q,j,s,l=",[mp.nstr(x,12) for x in (q,j,s,l)])
# exact lookback-time Taylor coefficients: tau(z)=int_0^z dz/((1+z)E)
E=lambda z: mp.sqrt(Om*(1+z)**3+OL)
c=mp.taylor(lambda z:1/((1+z)*E(z)),0,4)
taucoef=[c[n]/(n+1) for n in range(5)]
print("exact tau coeffs (D^0..D^4):",[mp.nstr(x,12) for x in taucoef])
Dz,dLc,Rc=pickle.load(open('coef.pkl','rb'))
Q,J,S,L=sp.symbols('q j s l')
sub={Q:sp.Float(str(q),30),J:sp.Float(str(j),30),S:sp.Float(str(s),30),L:sp.Float(str(l),30)}
print("formula D^n:",[sp.N(x.subs(sub),12) for x in Dz])
pr=(Dz[4]+sp.Rational(21,8)*Q**4).subs(sub)
print("printed D^4:",sp.N(pr,12))
# exact flat dL coefficients: (1+z) int_0^z dz/E
cI=mp.taylor(lambda z:1/E(z),0,5); I=[0]+[cI[n-1]/n for n in range(1,7)]
dl=[I[n+1]+I[n] for n in range(5)]
print("exact dL coeffs:",[mp.nstr(x,12) for x in dl])
print("formula dL:",[sp.N(x.subs(sub),12) for x in dLc])
