# Float scan (unchecked): min of a3/ln(10)^2 over cubics satisfying only the three one-sided ratio constraints
# r31, r35, r15 used by bn_a3_gen (kappa = 0.95499), per Omega; compare with the two-sided LP.
import mpmath as mp
from scipy.optimize import linprog
l2=float(mp.log(2)); K=0.95499
us=[l2/2,3*l2/2,5*l2/2]
def J(O,k): return float(mp.quad(lambda v:2/mp.sqrt(O+(1-O)*v**6),[2**(-k/4),1]))
for O in [0,0.25,0.5,0.75,0.9,1.0]:
  J1,J3,J5=J(O,1),J(O,3),J(O,5)
  # variables b2,b3 (natural-log coefficients): P_k = u+b2u^2+b3u^3
  def row(u): return [u*u,u**3],u
  (c1,d1),(c3,d3),(c5,d5)=[row(u) for u in us]
  A=[];b=[]
  # K J1 P3 <= 2 J3 P1 ; K J5 P3 <= 1/2 J3 P5 ; K J5 P1 <= 1/4 J1 P5
  for (Ja,Pa,Jb,Pb,r) in [(J1,(c3,d3),J3,(c1,d1),2),(J5,(c3,d3),J3,(c5,d5),0.5),(J5,(c1,d1),J1,(c5,d5),0.25)]:
    A.append([K*Ja*Pa[0][0]-r*Jb*Pb[0][0], K*Ja*Pa[0][1]-r*Jb*Pb[0][1]]); b.append(-(K*Ja*Pa[1]-r*Jb*Pb[1]))
  for (cc,dd) in [(c1,d1),(c3,d3),(c5,d5)]:
    A.append([-cc[0],-cc[1]]); b.append(dd)  # P>0
  r=linprog([0,1],A_ub=A,b_ub=b,bounds=[(None,None),(None,None)])
  print(O, r.status, r.x[1] if r.status==0 else None)
