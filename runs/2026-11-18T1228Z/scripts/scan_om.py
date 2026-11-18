# Float scan (not evidence): density bounds of fit_direction / rl19_box_unmatched (hyps 1, 2) and the
# lower bounds of the two-redshift headlines, with flat models of any density (generic model of this run).
exec(open('scan_flat.py').read().split("Zs=[sqrt(2)")[0])
Zs=[sqrt(2),2*sqrt(2),4*sqrt(2)]; xs=[log10(z) for z in Zs]
def fr(a,b,n): return [a+(b-a)*i/n for i in range(n+1)]
def dLf(O,Z): return Z*quad(lambda v: 2/sqrt(O+(1-O)*v**6), [sqrt(1/Z), 1])
# rl19 hyp 2 (Omega <= 1) and hyp 1 (0 <= Omega)
for lab,Os in [('Omega>1',fr(mpf(1),mpf(6),25)),('Omega<0',[mpf(-0.005),mpf(-0.004),mpf(-0.002),mpf(-0.001)])]:
    best=None
    for O in Os:
        d=[dLf(O,Z) for Z in Zs]
        for a2 in fr(3.43,3.49,3):
            for a3 in fr(1.57,1.69,3):
                s=spread(d,xs,a2,a3)
                if s is not None and (best is None or s<best[0]): best=(s,O,a2,a3)
    print('rl19',lab,[round(float(t),4) for t in best])
# fit_direction hyp 2 / hyp 1: need a cubic matching (spread<=0.1) with viol>=0
for lab,Os in [('Omega>1',fr(mpf(1),mpf(6),25)),('Omega<0',[mpf(-0.005),mpf(-0.002)])]:
    best=None
    for O in Os:
        d=[dLf(O,Z) for Z in Zs]
        for a2 in fr(-5,20,100):
            for a3 in fr(-10,20,120):
                s=spread(d,xs,a2,a3)
                if s is None or s>0.1: continue
                v=viol(O,a2,a3)
                if best is None or v>best[0]: best=(v,s,O,a2,a3)
    print('fit_direction',lab,[round(float(t),4) for t in best] if best else None)
