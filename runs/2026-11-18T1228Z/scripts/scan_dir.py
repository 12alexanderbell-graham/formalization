exec(open('scan_law.py').read().split('# (a)')[0])
Z3,Z7=mpf(4),mpf(8); x3,x7=log10(Z3),log10(Z7)
def viol_dir(m,k,O,e=0):
    d3=Z3*J(m,k,Z3); d7=Z7*J(m,k,Z7)
    r=d7/d3*mpf(10)**(mpf(e)/5); best=None
    for a3 in fr(-30,30,600):
        a2=(r*x3-x7-a3*(x7**3-r*x3**3))/(x7**2-r*x3**2)
        if B(a2,a3,x3)<=0 or B(a2,a3,x7)<=0: continue
        v=(a2-A2(O))-7*lam*(a3-A3(O))
        if best is None or v>best[0]: best=(v,a2,a3)
    return best
for m,k in [(1,0),(0.6,0),(0.5,0),(0.3,0),(0.3,-0.5),(0.5,-1),(0.34,-1)]:
    for O in [0.2,0.3,0.4]:
        v=viol_dir(mpf(m),mpf(k),mpf(O))
        print(m,k,O,[round(float(t),3) for t in v])
