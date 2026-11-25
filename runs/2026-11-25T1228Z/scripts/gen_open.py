"""Certificates for the open case of the curved pair (run 2026-11-25T1228Z): m in [1/10, 1], k in [0, 20].
Per parameter box [m0,m1]x[k0,k1]:
  L5(m,k) <= int_{W5L}^1 gC m k   (tangent cells, linear in m, k)
  int_{W3}^1 gC m k <= U3(m,k)    (chord cells, linear in m, k; y bounds for k >= 0)
and 27/10*U3 <= 2*L5 at the four corners. Exact rationals; Lean re-checks everything."""
from fractions import Fraction as F
import math, os, sys
W5L=F(420449,10**6); W3=F(594603,10**6)
N=int(os.environ.get("NC","20")); SC=10**6
KMAX=F(20)
def y(m,k,v): return m+k*v*v+(1-m-k)*v**6
def tangent(w,m0,m1,k0,k1):
    h=(1-w)/N; mc=(m0+m1)/2; kc=(k0+k1)/2; cs=[]
    A=F(0);B=F(0);C=F(0)
    for i in range(N):
        a=w+i*h; b=a+h; vm=float((a+b)/2)
        c=F(int(SC/math.sqrt(float(y(mc,kc,vm)))),SC); cs.append(int(c*SC))
        d3=(b**3-a**3)/3; d7=(b**7-a**7)/7
        A+=h*3*c - c**3*d7
        B+=h*c**3 - c**3*d7
        C+=c**3*d3 - c**3*d7
    return cs,A,B,C
def chord(w,m0,m1,k0,k1):
    h=(1-w)/N; ps=[];qs=[];ds=[]
    A=F(0);B=F(0);C=F(0)
    for i in range(N):
        a=w+i*h; b=a+h
        dlo=a*a-b**6
        dlo=F(math.floor(dlo*SC),SC) if dlo>0 else F(0)
        ylo=m0*(1-b**6)+k0*dlo+a**6
        yhi=m1*(1-a**6)+k1*(b*b-a**6)+b**6
        p=F(math.floor(math.sqrt(float(ylo))*SC)-1,SC)
        q=F(math.ceil(math.sqrt(float(yhi))*SC)+1,SC)
        assert p>0 and p*p<=ylo and yhi<=q*q
        ps.append(int(p*SC)); qs.append(int(q*SC)); ds.append(int(dlo*SC))
        g=2/(p*q*(p+q)); d3=(b**3-a**3)/3; d7=(b**7-a**7)/7
        A+=2*h/p - g*(d7 - h*p*p)
        B+=-g*(h - d7)
        C+=-g*(d3 - d7)
    return ps,qs,ds,A,B,C
def rd(x,s=10**9): return F(math.floor(x*s),s)
def ru(x,s=10**9): return F(math.ceil(x*s),s)
def box(m0,m1,k0,k1):
    cs,A5,B5,C5=tangent(W5L,m0,m1,k0,k1)
    p3,q3,d3,A3,B3,C3=chord(W3,m0,m1,k0,k1)
    corners=[(m,k) for m in (m0,m1) for k in (k0,k1)]
    # k >= 0: round each coefficient of k the safe way (the closed case had k <= 0)
    L=(rd(A5-F(1,10**8)),ru(B5),ru(C5))
    U=(ru(A3+F(1,10**8)),ru(B3),ru(C3))
    margins=[2*(L[0]-L[1]*m-L[2]*k) - F(27,10)*(U[0]+U[1]*m+U[2]*k) for m,k in corners]
    return dict(cs=cs,p3=p3,q3=q3,d3=d3,L=L,U=U,margin=min(margins))
def tree(m0,m1,k0,k1,depth=0):
    b=box(m0,m1,k0,k1)
    if b['margin']>F(1,1000) or depth>14:
        assert b['margin']>0, (m0,m1,k0,k1,float(b['margin']))
        return ('leaf',(m0,m1,k0,k1,b))
    if (m1-m0)/F(9,10) >= (k1-k0)/KMAX:
        mm=(m0+m1)/2; return ('m',mm,tree(m0,mm,k0,k1,depth+1),tree(mm,m1,k0,k1,depth+1))
    kk=(k0+k1)/2; return ('k',kk,tree(m0,m1,k0,kk,depth+1),tree(m0,m1,kk,k1,depth+1))
if __name__=='__main__':
    T=tree(F(1,10),F(1),F(0),KMAX)
    leaves=[]
    def col(t):
        if t[0]=='leaf': leaves.append(t[1])
        else: col(t[2]); col(t[3])
    col(T)
    print(len(leaves),'boxes; min margin',float(min(b['margin'] for *_,b in leaves)))
