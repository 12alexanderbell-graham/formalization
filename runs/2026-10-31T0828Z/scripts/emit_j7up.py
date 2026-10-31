"""Run 0828Z: secant certificate for an upper bound of J7(1/5) = ∫_{0.3535}^1 2/√(1/5 + 4/5 v⁶) dv
(left Riemann sum, N = 80; p_i ≤ √y_i ≤ q_i at the left endpoints). Prints the Lean lists and the
certified bound (exact arithmetic)."""
import math
from fractions import Fraction as Fr
D=10**5; O=Fr(1,5); w=Fr(3535,10000); N=80; h=(1-w)/N
def y(v): return O+(1-O)*v**6
ps=[];qs=[];S=Fr(0)
for i in range(N):
    v=w+i*h
    p=math.floor(math.sqrt(float(y(v)))*D); q=math.ceil(math.sqrt(float(y(v)))*D)
    while Fr(p,D)**2>y(v): p-=1
    while Fr(q,D)**2<y(v): q+=1
    ps.append(p);qs.append(q); P=Fr(p,D);Q=Fr(q,D)
    S+=h*2*(1/P-(y(v)-P**2)/(P*Q*(P+Q)))
print("h =",h, " sum ≈",float(S))
print("def pJ7 : List ℕ := ["+", ".join(map(str,ps))+"]")
print("def qJ7 : List ℕ := ["+", ".join(map(str,qs))+"]")
