# Exact-rational check (run 2026-11-21T1228Z) that the B1FitWitness enclosures at density 1/5 leave a box-corner cubic
# (a2 = 343/100, a3 = 117/20) matching within the 0.05-mag window; chose the witness of rl19_box_unmatched_h16.
from fractions import Fraction as F
J1=(F(1926847473,5000000000),F(385504523,1000000000))
J3=(F(1262414489,1000000000),F(3160225433,2500000000))
J5=(F(10060897683,5000000000),F(10078611121,5000000000))
t=(F(30101,100000),F(30105,100000))
def p(k,a2,a3,tt): return F(k,2)+a2*F(k*k,4)*tt+a3*F(k**3,8)*tt*tt
def rng(k,a2,a3): return (p(k,a2,a3,t[0]),p(k,a2,a3,t[1]))
import itertools
best=None
for a2 in [F(343,100),F(346,100),F(349,100)]:
  for a3n in range(560,610):
    a3=F(a3n,100)
    P1,P3,P5=rng(1,a2,a3),rng(3,a2,a3),rng(5,a2,a3)
    # X1/X3 = J1 p3/(2 J3 p1); X5/X3 = 2 J5 p3/(J3 p5)
    r1=(J1[0]*P3[0]/(2*J3[1]*P1[1]), J1[1]*P3[1]/(2*J3[0]*P1[0]))
    r5=(2*J5[0]*P3[0]/(J3[1]*P5[1]), 2*J5[1]*P3[1]/(J3[0]*P5[0]))
    lo=min(F(1),r1[0],r5[0]); hi=max(F(1),r1[1],r5[1])
    spread=hi/lo
    if best is None or spread<best[0]: best=(float(spread),a2,a3,[float(x) for x in r1+r5])
  print(best); best=None
print('window', 1.0225/0.978)
