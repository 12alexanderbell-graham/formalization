"""Aviles, Gruber, Luongo, Quevedo, arXiv:1204.2007 (PRD 86 (2012) 123516). Transcribed via WebFetch of arxiv.org/pdf
(offset reads) and ar5iv. Flat (k=0). Distances in units 1/H0 (c=1). Eq.(4),(12),(15), Appendix A."""
from common import *
import sympy as sp
R=sp.Rational
fl={Ok:0}
P={}
P['App.A dL(z)'] = ((z + z**2*(R(1,2)-q/2) + z**3*(-R(1,6)-j/6+q/6+q**2/2) + z**4*(R(1,12)+R(5,24)*j-q/12+R(5,12)*j*q-R(5,8)*q**2-R(5,8)*q**3+s/24)
   + z**5*(-R(1,20)-R(9,40)*j+j**2/12-l/120+q/20-R(11,12)*j*q+R(27,40)*q**2-R(7,8)*j*q**2+R(11,8)*q**3+R(7,8)*q**4-R(11,120)*s-q*s/8)), dist_family(0).subs(fl), z, 5)
P['App.A dF(z)'] = ((z - q/2*z**2 + z**3*(-R(1,24)-j/6+R(5,12)*q+q**2/2) + z**4*(R(1,24)+R(7,24)*j-R(17,48)*q+R(5,12)*j*q-R(7,8)*q**2-R(5,8)*q**3+s/24)
   + z**5*(-R(71,1920)-R(47,120)*j+j**2/12-l/120+R(149,480)*q-R(9,8)*j*q+R(47,40)*q**2-R(7,8)*j*q**2+R(27,16)*q**3+R(7,8)*q**4-R(9,80)*s-q*s/8)), dist_family(1).subs(fl), z, 5)
P['App.A dP(z)'] = ((z + z**2*(-R(1,2)-q/2) + z**3*(R(1,3)-j/6+R(2,3)*q+q**2/2) + z**4*(-R(1,4)+R(3,8)*j-R(3,4)*q+R(5,12)*j*q-R(9,8)*q**2-R(5,8)*q**3+s/24)
   + z**5*(R(1,5)-R(3,5)*j+j**2/12-l/120+R(4,5)*q-R(4,3)*j*q+R(9,5)*q**2-R(7,8)*j*q**2+2*q**3+R(7,8)*q**4-R(2,15)*s-q*s/8)), dist_family(2).subs(fl), z, 5)
P['App.A dQ(z)'] = ((z + z**2*(-1-q/2) + z**3*(R(23,24)-j/6+R(11,12)*q+q**2/2) + z**4*(-R(11,12)+R(11,24)*j-R(61,48)*q+R(5,12)*j*q-R(11,8)*q**2-R(5,8)*q**3+s/24)
   + z**5*(R(563,640)-R(17,20)*j+j**2/12-l/120+R(253,160)*q-R(37,24)*j*q+R(51,20)*q**2-R(7,8)*j*q**2+R(37,16)*q**3+R(7,8)*q**4-R(37,240)*s-q*s/8)), dist_family(3).subs(fl), z, 5)
if __name__=='__main__':
    for k_,(pr,rf,v,n) in P.items(): compare('AGLQ2012 '+k_, pr, rf, v, n)
    # Eq.(15) LCDM values vs exact (flat): from check_lcdm derivation
    Om,t=sp.symbols('Omega_m t'); A=sp.symbols('A')
    adot=A*sp.sqrt(Om/A**3+1-Om); ders=[A,adot]
    for n in range(2,7): ders.append(sp.diff(ders[-1],A)*adot)
    v=[sp.expand(sp.simplify(d.subs(A,1))) for d in ders]
    exact=dict(q=-v[2],j=v[3],s=v[4],l=v[5],m=v[6])
    printed=dict(q=-1+R(3,2)*Om, j=1, s=1-R(9,2)*Om, l=1+3*Om-R(27,2)*Om**2, m=1-R(27,2)*Om**2-81*Om**2-R(81,2)*Om**3)
    for k_ in exact: 
        d=sp.expand(printed[k_]-exact[k_]); print(('OK   ' if d==0 else 'DIFF ')+'AGLQ2012 eq15 %s0(LCDM): exact %s'%(k_,exact[k_]), '' if d==0 else '| printed-exact = %s'%d)
    # Eq.(4) and Eq.(12): generic a(t), units 8piG/3 = 1 (flat) -> P = -(2 addot/a + H^2)/3
    Af=sp.Function('A')(t); H=Af.diff(t)/Af
    qf=-Af.diff(t,2)/Af/H**2; jf=Af.diff(t,3)/Af/H**3; sf=Af.diff(t,4)/Af/H**4; lf=Af.diff(t,5)/Af/H**5; mf=Af.diff(t,6)/Af/H**6
    chk={'4q':(qf,-H.diff(t)/H**2-1),'4j':(jf,H.diff(t,2)/H**3-3*qf-2),'4s':(sf,H.diff(t,3)/H**4+4*jf+3*qf*(qf+4)+6),
         '4l':(lf,H.diff(t,4)/H**5-24-60*qf-30*qf**2-10*jf*(qf+2)+5*sf),
         '4m':(mf,H.diff(t,5)/H**6+10*jf**2+120*jf*(qf+1)+3*(2*lf+5*(24*qf+18*qf**2+2*qf**3-2*sf-qf*sf+8)))}
    Pf=-(2*Af.diff(t,2)/Af+H**2)/3
    chk.update({'12P':(Pf,H**2*(2*qf-1)/3),'12dP':(Pf.diff(t),R(2,3)*H**3*(1-jf)),'12d2P':(Pf.diff(t,2),R(2,3)*H**4*(jf-3*qf-sf-3)),
       '12d3P':(Pf.diff(t,3),R(2,3)*H**5*(2*sf+jf-lf+qf*(21-jf)+6*qf**2+12)),
       '12d4P':(Pf.diff(t,4),R(2,3)*H**6*(jf**2+3*lf-mf-144*qf-81*qf**2-6*qf**3-12*jf*(2+qf)-3*sf-3*qf*sf-60))})
    X=sp.symbols('X0:7')
    for k_,(lhs,rhs) in chk.items():
        d=sp.simplify(lhs-rhs)
        if d!=0:
            # express residual in q,j,s,l,m with H=1 for readability
            rep={Af.diff(t,n):X[n] for n in range(6,0,-1)}; dd=sp.simplify(d.subs(rep).subs(Af,1).subs(X[1],1))
            dd=dd.subs({X[2]:-q,X[3]:j,X[4]:s,X[5]:l,X[6]:m}) if True else dd
            print('DIFF AGLQ2012 eq'+k_, '(lhs-rhs at a=H=1):', sp.expand(dd))
        else: print('OK   AGLQ2012 eq'+k_)
