import sys; sys.path.insert(0,'/home/claude/formalization/runs/2026-11-21T0428Z/referee/scripts')
import sys; sys.argv=['x','60','60','0.1']
import taylor
from mpmath import mp, mpf, nstr
res = taylor.run(smax=mpf(10)**7, nturn=7)
for i,(z,l) in enumerate(res): print(i, nstr(z,35), nstr(l,35))
bands = {0:('3.321992118','3.321992119'),1:('1.664155','1.664157'),2:('2.10852','2.10858'),3:('1.967422','1.967510'),4:('2.009926','2.010028')}
for k,(lo,hi) in bands.items():
    lo,hi=mpf(lo),mpf(hi); l=res[k][1]; c=(lo+hi)/2; r=(hi-lo)/2
    print(k,'in band',lo<=l<=hi,'lower margin',nstr(l-lo,6),'upper margin',nstr(hi-l,6),
          '| tenth-width band [%s,%s] contains:'%(nstr(c-r/10,10),nstr(c+r/10,10)), c-r/10<=l<=c+r/10,
          ' |l-c|/r =',nstr(abs(l-c)/r,4))
z0=res[0][0]; print('zeta0 margins', nstr(z0-mpf('4.071496844'),6), nstr(mpf('4.071496845')-z0,6))
