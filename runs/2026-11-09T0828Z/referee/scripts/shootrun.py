import mpmath as mp, sys
import taylor
from taylor import *
cfg=sys.argv[1]
if cfg=='A': mp.mp.dps=50; kw=dict(h=mp.mpf(1)/32,N=30,smax=12)
else: mp.mp.dps=65; kw=dict(h=mp.mpf(1)/20,N=42,smax=12,sub=10)
lo,hi,el,eh=shoot(mp.mpf('1.0'),mp.mpf('1.02'),tol=mp.mpf('1e-32'),**kw)
print(cfg,'upper',el,eh,mp.nstr(lo,34),mp.nstr(hi,34))
lo,hi,el,eh=shoot(mp.mpf('-0.45'),mp.mpf('-0.44'),tol=mp.mpf('1e-32'),**kw)
print(cfg,'lower',el,eh,mp.nstr(lo,34),mp.nstr(hi,34))
