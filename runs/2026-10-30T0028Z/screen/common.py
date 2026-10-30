import sympy as sp, pickle, os
z,y,q,j,s,l,Ok = sp.symbols('z y q j s l Omega_k')
_d=os.path.dirname(os.path.abspath(__file__))
REF,REFY = pickle.load(open(os.path.join(_d,'ref.pkl'),'rb'))
def ser(e, v, n):
    return sp.expand(sp.series(e, v, 0, n).removeO())
def dist_family(n, var='z'):
    """d_L/(1+z)^(n/2) in units c/H0 ; n=0 dL, 1 dF, 2 dP, 3 dQ, 4 dA"""
    e = REF['dL']*(1+z)**sp.Rational(-n,2)
    e = ser(e, z, 6)
    if var=='y': e = ser(e.subs(z, y/(1-y)), y, 6)
    return e
def lnfamily(n, var='z'):
    e = ser(REF['lnDLoverZ'] - sp.Rational(n,2)*sp.log(1+z), z, 5)
    if var=='y':  # ln(d/y) = ln(d/z) + ln(z/y) = ln(d/z) + ln(1+z)= ..; z/y = 1+z = 1/(1-y)
        e = ser(e.subs(z, y/(1-y)) - sp.log(1-y), y, 5)
    return e
def compare(label, printed, ref, v, upto):
    """printed, ref: series in v; compare coefficients v^0..v^upto"""
    out=[]
    ok=True
    for i in range(0,upto+1):
        d = sp.simplify(sp.expand(printed).coeff(v,i) - sp.expand(ref).coeff(v,i))
        if d!=0:
            ok=False
            out.append('   %s^%d: printed %s | ref %s | diff %s'%(v,i,sp.factor(sp.expand(printed).coeff(v,i)),sp.factor(sp.expand(ref).coeff(v,i)),sp.factor(d)))
    print(('OK   ' if ok else 'DIFF ')+label+' (through %s^%d)'%(v,upto))
    for o in out: print(o)
    return ok
