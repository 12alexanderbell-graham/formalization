import math
exec(open(__file__.replace('opt_float.py','feas_wide.py')).read().split('def ok')[0])
def F(m,l):
    ys=[y(z,m,l) for z,h,s in T]
    if min(ys)<0: return 1e9
    a=alpha(m,l); b=w0*73+sum(h/s/s*math.sqrt(yy) for (z,h,s),yy in zip(T,ys))
    return gamma-b*b/a, b/a
best=(1e9,0,0)
m,l=0.436,0.981; st=0.01
while st>1e-9:
    imp=False
    for dm,dl in [(st,0),(-st,0),(0,st),(0,-st)]:
        v=F(m+dm,l+dl)[0]
        if v<F(m,l)[0]: m,l=m+dm,l+dl; imp=True
    if not imp: st/=2
print(m,l,F(m,l))
