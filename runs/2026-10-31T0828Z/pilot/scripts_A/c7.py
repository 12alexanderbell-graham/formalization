import numpy as np
rng=np.random.default_rng(2)
def nroots(u,w):
    r=np.roots([1,-3,-3*(u+w),-(u*u+u*w-w)])
    return sum(1 for z in r if abs(z.imag)<1e-9 and z.real>1+1e-12)
from collections import Counter
c=Counter()
for _ in range(100000):
    u=rng.uniform(-8,8);w=rng.uniform(-8,12)
    c[(u>-2, 1+u+w>0, nroots(u,w))]+=1
print(sorted(c.items()))
