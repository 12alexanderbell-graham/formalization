from mpmath import mp, quad, sqrt, log, mpf
mp.dps=30
def chi(O,z): return quad(lambda t: 1/sqrt(O*(1+t)**3+1-O),[0,z])
def b(O):
    return [1, mpf(3)/2-mpf(3)/4*O, mpf(7)/6-2*O+mpf(9)/8*O**2, -(135*O**3-288*O**2+188*O-40)/mpf(64)]
for O in [0.25,0.3,0.35]:
    O=mpf(O); bb=b(O)
    row=[]
    for z in [0.5,1,1.4,2,3,4,5,6,7]:
        u=log(1+z); D=(1+z)*chi(O,z)
        p3=u+bb[1]*u**2+bb[2]*u**3; p4=p3+bb[3]*u**4
        row.append((z, float(5*mp.log10(D/p3)), float(5*mp.log10(D/p4))))
    print(float(O)); [print('  z=%4.1f  dmu3=%+.4f dmu4=%+.4f'%r) for r in row]
