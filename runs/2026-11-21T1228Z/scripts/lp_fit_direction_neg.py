# Float LP study (unchecked; run 2026-11-21T1228Z): the minimum of 20/3 e3 - e2 for fit_direction at negative density
# from the residual constraints and enclosures of the three distance integrals; chose the bounds used in NecessityBN.
import mpmath as mp
from scipy.optimize import linprog
mp.mp.dps=30
l=mp.log(2)
def Q(O,u): return u+(mp.mpf(3)/2-mp.mpf(3)/4*O)*u**2+(mp.mpf(9)/8*O**2-2*O+mp.mpf(7)/6)*u**3
kap=0.95499
def lp(O,J1l,J1u,J3u,J5l,J3l=None):
    O=mp.mpf(O)
    Q1,Q3,Q5=[float(Q(O,k*l/2)) for k in (1,3,5)]
    c=[(1/4,1/8),(9/4,27/8),(25/4,125/8)]; Qs=[Q1,Q3,Q5]
    A=[];b=[]
    def le(i,j,r):  # P_i <= r P_j
        A.append([c[i][0]-r*c[j][0], c[i][1]-r*c[j][1]]); b.append(r*Qs[j]-Qs[i])
    le(0,2,0.25*J1u/(kap*J5l))
    le(1,2,0.5*J3u/(kap*J5l))
    # r31: kap J1 P3 <= 2 J3 P1 -> P3 <= 2 J3u/(kap J1l) P1
    le(1,0,2*J3u/(kap*J1l))
    for i in range(3): A.append([-c[i][0],-c[i][1]]); b.append(Qs[i])  # P_i>=0
    res=linprog([-1,20/3],A_ub=A,b_ub=b,bounds=[(None,None)]*2)
    return res.fun, res.x
def J(O,w): return float(mp.quad(lambda v:2/mp.sqrt(O+(1-O)*v**6),[w,1]))
Om=-1/((4*mp.sqrt(2))**3-1)
w1=mp.sqrt(1/mp.sqrt(2)); w3=mp.sqrt(1/(2*mp.sqrt(2))); w5=mp.sqrt(1/(4*mp.sqrt(2)))
for O in [0,Om/2,Om*mp.mpf('0.999')]:
    print(float(O),'true',lp(O,J(O,w1),J(O,w1),J(O,w3),J(O,w5)))
def fac(O,w): return mp.sqrt(w**6/(O+(1-O)*w**6))
U1=float(fac(Om,w1)*(mp.sqrt(2)-1)); U3=float(fac(Om,w3)*(2*mp.sqrt(2)-1)); L5=float(1/mp.mpf('0.4205')**2-1)
for O in [0,Om]:
    print(float(O),'crude',lp(O,float(mp.sqrt(2)-1),U1,U3,L5))
print('---')
for (J1l,U1,U3,L5) in [(0.414,0.4164,1.95,4.655),(0.414,0.42,2.0,4.6),(0.41,0.43,2.1,4.5)]:
    for O in [0,Om]:
        r=lp(O,J1l,U1,U3,L5); print(J1l,U1,U3,L5,float(O),r)
print('===')
import numpy as np
def lpd(O,J1l,J1u,J3u,J5l):
    O=mp.mpf(O)
    Q1,Q3,Q5=[float(Q(O,k*l/2)) for k in (1,3,5)]
    c=[(1/4,1/8),(9/4,27/8),(25/4,125/8)]; Qs=[Q1,Q3,Q5]
    A=[];b=[]
    def le(i,j,r):
        A.append([c[i][0]-r*c[j][0], c[i][1]-r*c[j][1]]); b.append(r*Qs[j]-Qs[i])
    le(0,2,0.25*J1u/(kap*J5l)); le(1,2,0.5*J3u/(kap*J5l)); le(1,0,2*J3u/(kap*J1l))
    for i in range(3): A.append([-c[i][0],-c[i][1]]); b.append(Qs[i])
    res=linprog([-1,20/3],A_ub=A,b_ub=b,bounds=[(None,None)]*2)
    return res.fun, res.ineqlin.marginals
for O in [0,-1/180]: print(lpd(O,0.414,0.42,2.0,4.5))
