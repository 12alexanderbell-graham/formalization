"""Certificates for Work/Cosmography/B1L19CurvedCerts.lean (run 2026-11-04T2028Z).
For each box [m0,m1]x[k0,k1] of the domain m in [1/10,1], k in [-1/10,0]:
  L5(m,k) <= int_{W5L}^1 gC  (tangent cells, linear in m,k),
  int_{W5U}^1 gC <= Ub        (chord cells, constant),
  int_{W3}^1 gC <= U3(m,k)    (chord cells, linear),
and the check 27/10*U3 <= 2*L5 - 2*(-k)*Ub^3/4 at the 4 corners (linear in m,k), (1/10)*Ub^2 <= 1.
Exact rational arithmetic (fractions); Lean re-checks everything."""
from fractions import Fraction as F
import math, sys
W5L=F(420449,10**6); W5U=F(420448,10**6); W3=F(594603,10**6)
N=int(__import__("os").environ.get("NC","20")); SC=10**6
def y(m,k,v): return m+k*v*v+(1-m-k)*v**6
def tangent(w,m0,m1,k0,k1):
    h=(1-w)/N; mc=(m0+m1)/2; kc=(k0+k1)/2; cs=[]
    A=F(0);B=F(0);C=F(0)  # sum = A - B m - C k
    for i in range(N):
        a=w+i*h; b=a+h; vm=float((a+b)/2)
        c=F(int(SC/math.sqrt(float(y(mc,kc,vm)))),SC); cs.append(int(c*SC))
        # h*(3c - c^3 m) - c^3 k (b^3-a^3)/3 - c^3 (1-m-k)(b^7-a^7)/7
        d3=(b**3-a**3)/3; d7=(b**7-a**7)/7
        A+=h*3*c - c**3*d7
        B+=h*c**3 - c**3*d7
        C+=c**3*d3 - c**3*d7
    return cs,A,B,C
def chord(w,m0,m1,k0,k1):
    h=(1-w)/N; ps=[];qs=[];ds=[]
    A=F(0);B=F(0);C=F(0) # sum = A + B m + C k
    for i in range(N):
        a=w+i*h; b=a+h
        dlo=a*a-b**6
        if dlo<0: dlo=F(0)
        dlo=F(math.floor(dlo*SC),SC) if dlo>0 else F(0)
        ylo=m0*(1-b**6)+k0*(b*b-a**6)+a**6
        yhi=m1*(1-a**6)+k1*dlo+b**6
        p=F(math.floor(math.sqrt(float(ylo))*SC)-1,SC)
        q=F(math.ceil(math.sqrt(float(yhi))*SC)+1,SC)
        assert p>0 and p*p<=ylo and yhi<=q*q
        ps.append(int(p*SC)); qs.append(int(q*SC)); ds.append(int(dlo*SC))
        g=2/(p*q*(p+q)); d3=(b**3-a**3)/3; d7=(b**7-a**7)/7
        # 2h/p - g*(h m + k d3 + (1-m-k) d7 - h p^2)
        A+=2*h/p - g*(d7 - h*p*p)
        B+=-g*(h - d7)
        C+=-g*(d3 - d7)
    return ps,qs,ds,A,B,C
def rd(x,s=10**9): return F(math.floor(x*s),s)
def ru(x,s=10**9): return F(math.ceil(x*s),s)
def box(m0,m1,k0,k1):
    cs,A5,B5,C5=tangent(W5L,m0,m1,k0,k1)
    p5,q5,d5,a5,b5,c5=chord(W5U,m0,m1,k0,k1)
    p3,q3,d3,A3,B3,C3=chord(W3,m0,m1,k0,k1)
    corners=[(m,k) for m in (m0,m1) for k in (k0,k1)]
    Ub=ru(max(a5+b5*m+c5*k for m,k in corners),10**6)
    # rounded coefficient forms used in Lean
    L=(rd(A5-F(1,10**8)),ru(B5),rd(C5))
    U=(ru(A3+F(1,10**8)),ru(B3),rd(C3))
    margins=[2*(L[0]-L[1]*m-L[2]*k) - 2*(-k)*Ub**3/4 - F(27,10)*(U[0]+U[1]*m+U[2]*k) for m,k in corners]
    return dict(c5=(A5,B5,C5),c3=(A3,B3,C3),u5=(a5,b5,c5),cs=cs,p5=p5,q5=q5,d5=d5,p3=p3,q3=q3,d3=d3,L=L,U=U,Ub=Ub,margin=min(margins))
if __name__=='__main__':
    M=int(sys.argv[1]); K=int(sys.argv[2])
    worst=None
    for i in range(M):
        for j in range(K):
            m0=F(1,10)+F(9,10)*i/M; m1=F(1,10)+F(9,10)*(i+1)/M
            k0=-F(1,10)+F(1,10)*j/K; k1=-F(1,10)+F(1,10)*(j+1)/K
            b=box(m0,m1,k0,k1)
            print(float(m0),float(k0),'margin %.4f'%float(b['margin']),'Ub',float(b['Ub']))

def adaptive(m0,m1,k0,k1,depth=0,out=None):
    if out is None: out=[]
    b=box(m0,m1,k0,k1)
    if b['margin']>F(1,1000) or depth>12:
        out.append((m0,m1,k0,k1,b)); return out
    # split the longer side relative to its scale
    if (m1-m0)/F(9,10) >= (k1-k0)/F(1,10):
        mm=(m0+m1)/2; adaptive(m0,mm,k0,k1,depth+1,out); adaptive(mm,m1,k0,k1,depth+1,out)
    else:
        kk=(k0+k1)/2; adaptive(m0,m1,k0,kk,depth+1,out); adaptive(m0,m1,kk,k1,depth+1,out)
    return out
