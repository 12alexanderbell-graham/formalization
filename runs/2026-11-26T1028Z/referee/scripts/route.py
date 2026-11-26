# Worst-case margins of the planned route, pi in [3.141592,3.141593], sqrt7 in [2.64575,2.6458], eps <= 1386e-6
from mpmath import iv, mpf
iv.dps = 30
PI = iv.mpf(['3.141592','3.141593']); R7 = iv.mpf(['2.64575','2.6458'])
E = iv.mpf('0.001386')  # monotone in eps, worst case at max eps
# (a) eps' <= eps*exp(-(1-36e)L/2), L >= pi/(r7/2+16e)
Lmin = PI/(R7/2+16*E); Lmax = PI/(R7/2-16*E)
expo = (1-36*E)*Lmin/2
print("(a) exponent >=", expo.a, " factor <=", iv.exp(-expo).b, " margin to .33:", 0.33-iv.exp(-expo).b)
# (b) |L - 2pi/r7| / eps
c = 2*PI/R7
dLb = iv.mpf([0, max((Lmax-c).b, (c-Lmin).b)])/E
print("(b) |L-2pi/r7|/eps <=", dLb.b, "(claim 30)  exp(2pi/r7) in", iv.exp(c), " 11.2*30 =", 11.2*30)
# (c) |D/2 + pi/r7| <= |L/2 - pi/r7| + 18 e L
half = max((Lmax/2-PI/R7).b, (PI/R7-Lmin/2).b)
dc = (half + 18*E*Lmax)/E
print("(c) |D/2+pi/r7|/eps <=", dc.b, "(claim 59)  exp(-pi/r7) in", iv.exp(-PI/R7), " .33*59 =", 0.33*59)
print("(d) 336*eps0 =", 336*1386e-6, "<= .47 ;  20*eps0 =", 20*1386e-6, "<= .03")
