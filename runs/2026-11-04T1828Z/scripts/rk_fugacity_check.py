from mpmath import mp,mpf,polyroots,log,findroot,log10,cbrt
mp.dps=30
Ob=(cbrt(2)-1)/3; Oa=1/(9*(cbrt(2)-1))
Tr=mpf('0.7')
def d(Pr):
    A=Oa*Pr/Tr**mpf('2.5'); B=Ob*Pr/Tr
    r=sorted([z.real for z in polyroots([1,-1,A-B-B*B,-A*B]) if abs(z.imag)<1e-25 and z.real>B])
    zl,zv=r[0],r[-1]
    f=lambda Z: Z-1-log(Z-B)-(A/B)*log(1+B/Z)
    return f(zl)-f(zv)
p=findroot(d,mpf('0.087'))
print(p, -log10(p)-1)
for i in range(5,20):
    Pr=mpf(i)/100
    print(Pr, d(Pr))
