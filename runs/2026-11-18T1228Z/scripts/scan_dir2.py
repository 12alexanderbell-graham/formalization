exec(open('scan_law.py').read().split('# (a)')[0])
Z3,Z7=mpf(4),mpf(8); x3,x7=log10(Z3),log10(Z7)
def ratio(m,k): return (Z7*J(m,k,Z7))/(Z3*J(m,k,Z3))
def line_pts(r):
    for a3 in fr(-40,200,4800):
        a2=(r*x3-x7-a3*(x7**3-r*x3**3))/(x7**2-r*x3**2)
        if B(a2,a3,x3)>0 and B(a2,a3,x7)>0: yield a2,a3
for lab,m,k in [('EdS',1,0),('m=.8',0.8,0),('m=.6',0.6,0),('m=.45',0.45,0)]:
    r0=ratio(mpf(m),mpf(k))
    best_dir=None; best_sep=None
    for e in fr(mpf(-0.1),mpf(0.1),20):
        r=r0*mpf(10)**(e/5)
        for a2,a3 in line_pts(r):
            for O in fr(mpf(0.2),mpf(0.4),4):
                v=(a2-A2(O))-7*lam*(a3-A3(O))
                dd=(a2-A2(O))**2+(a3-A3(O))**2
                if best_dir is None or v>best_dir[0]: best_dir=(v,e,O,a2,a3)
                if best_sep is None or dd<best_sep[0]: best_sep=(dd,e,O,a2,a3)
    print(lab,'r',round(float(r0),4),'dir',[round(float(t),3) for t in best_dir],'sep d^2 (need<=1.5625)',[round(float(t),3) for t in best_sep])
