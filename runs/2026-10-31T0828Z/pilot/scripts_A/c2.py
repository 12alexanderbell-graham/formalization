import numpy as np
rng=np.random.default_rng(1)
def nroots(u,w):
    r=np.roots([1,-3,-3*(u+w),-(u*u+u*w-w)])
    return sum(1 for z in r if abs(z.imag)<1e-9 and z.real>1+1e-12)
from collections import Counter
c=Counter(); ex={}
for _ in range(200000):
    u=rng.uniform(-6,6);w=rng.uniform(-8,8)
    if not(-2<u and 1+u+w>0): continue
    k=(nroots(u,w), u+w<-1)
    c[k]+=1; ex.setdefault(k,(u,w))
print(c,ex)
c=Counter()
for _ in range(200000):
    u=rng.uniform(-6,6);w=rng.uniform(-8,8)
    if not(-2<u and 1+u+w>0): continue
    c[nroots(u,w)]+=1
print(c)
