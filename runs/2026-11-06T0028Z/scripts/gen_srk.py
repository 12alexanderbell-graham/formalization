"""Certificates for the SRK (Soave 1972 kappa at omega = 1) acentric-factor window (run 2026-11-06T0028Z).
Generated from runs/2026-11-04T1828Z/scripts/gen_rk.py by make_gen_srk (same RK isotherm; theta = 0.7 K/alpha,
alpha = (1 + kappa(1 - sqrt 0.7))^2, kappa = 0.480 + 1.574 - 0.176 = 1.878; spinodal windows moved). Exact rationals."""
import sys
from fractions import Fraction as F
from mpmath import mp, mpf, sqrt, cbrt, log, polyroots
mp.dps = 50
# critical root x_c of x^3-3x^2-3x-1, bounds
c = cbrt(mpf(2)); xc = c*c + c + 1
X0 = F(384732210, 10**8); X1 = F(384732211, 10**8)
f = lambda x: x**3 - 3*x**2 - 3*x - 1
assert f(X0) < 0 < f(X1)
# sqrt(7/10) bounds
S0 = F(836660026, 10**9); S1 = F(836660027, 10**9)
assert S0*S0 < F(7,10) < S1*S1
# K = R Tc b / a_c = 3x - 9 - 9/x increasing in x
K = lambda x: 3*x - 9 - 9/x
K0, K1 = K(X0), K(X1)
import json as _json
VAR = _json.load(open(sys.argv[3])) if len(sys.argv) > 3 else {'tag': 'srk', 'kappa': [1878, 1000], 'ratio': [1020, 100000], 'ratio_k': 4, 'omega': [992, 1000], 'omega_k': 3}
TAG = VAR['tag']
KAP = F(*VAR['kappa'])
AL0 = (1 + KAP*(1 - S1))**2; AL1 = (1 + KAP*(1 - S0))**2
TH0 = F(7,10)*K0/AL1; TH1 = F(7,10)*K1/AL0
def rnd(fr, d, up):
    import math
    v = fr*10**d
    n = math.ceil(v) if up else math.floor(v)
    return F(n, 10**d)
T0 = rnd(TH0, 10, False); T1 = rnd(TH1, 10, True)
print('theta in', float(T0), float(T1), float(T1-T0))
th = mpf(7)/10*(3*xc-9-9/xc)/(1 + mpf(KAP.numerator)/KAP.denominator*(1 - sqrt(mpf(7)/10)))**2
assert mpf(T0.numerator)/T0.denominator < th < mpf(T1.numerator)/T1.denominator
# q pieces
def qplus(x): return (2*x+1)*(x-1)**2
def qminus(x): return (x*x+x)**2
def qneg_ok(a,b): return qplus(b) < T0*qminus(a)
def qpos_ok(a,b): return qplus(a) > T1*qminus(b)
def dpos_ok(a,b): return 6*a*(a-1) > 2*T1*b*(b+1)*(2*b+1)
def dneg_ok(a,b): return 6*b*(b-1) < 2*T0*a*(a+1)*(2*a+1)
def cover(lo, hi, ok, step0):
    pts=[lo]; x=lo
    while x < hi:
        s = step0
        while True:
            y = min(hi, x+s)
            if ok(x,y): break
            s = s/2
            assert s > F(1,10**6), (float(x),)
        pts.append(y); x = y
    return pts
W1a, W1b, W2a, W2b, XF = F(7,5), F(17,10), F(19), F(25), F(30)
P_qneg1 = cover(F(1), W1a, qneg_ok, F(1,10))
P_d1 = cover(W1a, W1b, dpos_ok, F(1,20))
P_qpos = cover(W1b, W2a, qpos_ok, F(1))
P_d2 = cover(W2a, W2b, dneg_ok, F(1))
P_qneg2 = cover(W2b, XF, qneg_ok, F(1))
assert T0*XF > 2 and T0*XF*XF >= 2*XF + 1
for n,p in [('qneg1',P_qneg1),('d1',P_d1),('qpos',P_qpos),('d2',P_d2),('qneg2',P_qneg2)]:
    print(n, len(p)-1, [str(x) for x in p])

# ---------- window certificate ----------
def m(fr): return mpf(fr.numerator)/fr.denominator
def g(t,x): return t/(x-1) - 1/(x*x+x)
def roots(p,t):
    r=sorted([z.real for z in polyroots([p,-t,-p-t+1,-1], maxsteps=400, extraprec=300) if abs(z.imag)<mpf(10)**-40 and z.real>1])
    return r
PLO_N, PHI_N = int(sys.argv[1]), int(sys.argv[2])
PLO = F(PLO_N,10**10); PHI = F(PHI_N,10**10)
import sys

def sigfig(v, up, d=7):
    # rational with d decimals after point scaled
    import math
    s = 10**d
    n = math.ceil(v*s) if up else math.floor(v*s)
    return F(int(n), s)
rl0 = roots(m(PLO), m(T0)); rl1 = roots(m(PLO), m(T1))
# lower: a1 < xl, b1 > xl
xl_lo = min(rl0[0], rl1[0]); xl_hi = max(rl0[0], rl1[0])
A1 = sigfig(xl_lo, False); B1 = sigfig(xl_hi, True)
xg = min(rl0[2], rl1[2]); A3 = sigfig(xg, False, 4)
assert g(T0,A1) > PLO and g(T1,B1) < PLO and g(T0,A3) > PLO
rh0 = roots(m(PHI), m(T0)); rh1 = roots(m(PHI), m(T1))
B1h = sigfig(max(rh0[0],rh1[0]), True)
A3h = sigfig(min(rh0[2],rh1[2]), False, 4); B3h = sigfig(max(rh0[2],rh1[2]), True, 4)
assert g(T1,B1h) < PHI and g(T0,A3h) > PHI and g(T1,B3h) < PHI
print('A1,B1,A3', A1, B1, A3, ' B1h,A3h,B3h', B1h, A3h, B3h)
def Klo(t):
    L1 = log(m((A3-1)/(B1-1))); L2 = log(m((A3+1)*B1/(A3*(B1+1))))
    psi = t*L1 + L2 - m(PLO)*(m(A3)-m(B1))
    return psi - (m(B1)-m(A1))*(m(PLO) - g(t,m(B1)))
def Khi(t):
    L1 = log(m((B3h-1)/(B1h-1))); L2 = log(m((B3h+1)*B1h/(B3h*(B1h+1))))
    psi = t*L1 + L2 - m(PHI)*(m(B3h)-m(B1h))
    return psi + (m(B3h)-m(A3h))*(m(PHI) - g(t,m(B3h)))
print('Klo', Klo(m(T0)), Klo(m(T1)), 'Khi', Khi(m(T0)), Khi(m(T1)))

# ---------- Lean emission ----------
import math
LOG2LO = F(6931471803, 10**10); LOG2HI = F(6931471808, 10**10)
def q(fr): return f"({fr.numerator} / {fr.denominator} : ℝ)" if fr.denominator != 1 else f"({fr.numerator} : ℝ)"
def lit(fr): return f"{fr.numerator} / {fr.denominator}" if fr.denominator != 1 else f"{fr.numerator}"
def logcert(r):
    """r rational > 0: r = 2^k (1-t0) y; returns (k,t0,y,n, lo, hi) with lo < log r < hi (exact rational check)."""
    lr = log(m(r)); k = int(round(float(lr/log(2))))
    t = 1 - m(r)/mpf(2)**k
    t0 = F(int(round(float(t)*10**5)), 10**5)
    y = r / (F(2)**k * (1 - t0)) if k >= 0 else r * F(2)**(-k) / (1 - t0)
    at = abs(t0)
    n = 1
    while at**(n+1)/(1-at) > F(1, 10**11): n += 1
    S = sum(t0**(i+1)/(i+1) for i in range(n)); E = at**(n+1)/(1-at)
    # log(1-t0) in [-S-E, -S+E]; log y in [1-1/y, y-1]
    if k >= 0: l2lo, l2hi = k*LOG2LO, k*LOG2HI
    else: l2lo, l2hi = k*LOG2HI, k*LOG2LO
    lo = l2lo - S - E + (1 - 1/y); hi = l2hi - S + E + (y - 1)
    lo = F(math.floor(lo*10**12), 10**12); hi = F(math.ceil(hi*10**12), 10**12)
    assert m(lo) < lr < m(hi)
    assert lo < hi
    return k, t0, y, n, lo, hi

def emit_log(name, rexpr, r, want):
    """Lemma `lo < Real.log (rexpr)` or `Real.log (rexpr) < hi`; rexpr evaluates to rational r."""
    k,t0,y,n,lo,hi = logcert(r)
    concl = f"{lit(lo)} < Real.log ({rexpr})" if want=='lo' else f"Real.log ({rexpr}) < {lit(hi)}"
    if k >= 0:
        fac = f"(2:ℝ) ^ {k} * (1 - ({lit(t0)})) * ({lit(y)})"
        rw = "Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_pow"
    else:
        fac = f"(1 - ({lit(t0)})) / (2:ℝ) ^ {-k} * ({lit(y)})"
        rw = "Real.log_mul (by norm_num) (by norm_num), Real.log_div (by norm_num) (by norm_num), Real.log_pow"
    txt = f"""lemma {name} : {concl} := by
  have e : ({rexpr} : ℝ) = {fac} := by norm_num
  rw [e, {rw}]
  have h := log_series' ({lit(t0)}) (by norm_num [abs_lt]) {n}
  rw [abs_le] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  have u1 : Real.log ({lit(y)} : ℝ) ≤ {lit(y)} - 1 := Real.log_le_sub_one_of_pos (by norm_num)
  have u2 : 1 - ({lit(y)} : ℝ)⁻¹ ≤ Real.log ({lit(y)}) := Real.one_sub_inv_le_log_of_pos (by norm_num)
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  push_cast
  norm_num at h u1 u2 ⊢
  linarith [h.1, h.2]
"""
    return txt, (lo if want=='lo' else hi)

out = []
L = lambda fr: '(' + lit(fr) + ')'
# log lemmas
rA = (A3-1)/(B1-1); rB = (A3+1)*B1/(A3*(B1+1))
rC = (B3h-1)/(B1h-1); rD = (B3h+1)*B1h/(B3h*(B1h+1))
tA, lA = emit_log('logA_lo', f"({L(A3)} - 1) / ({L(B1)} - 1)", rA, 'lo')
tB, lB = emit_log('logB_lo', f"(({L(A3)} + 1) / {L(A3)}) / (({L(B1)} + 1) / {L(B1)})", rB, 'lo')
tC, uC = emit_log('logC_hi', f"({L(B3h)} - 1) / ({L(B1h)} - 1)", rC, 'hi')
tD, uD = emit_log('logD_hi', f"(({L(B3h)} + 1) / {L(B3h)}) / (({L(B1h)} + 1) / {L(B1h)})", rD, 'hi')
out += [tA,tB,tC,tD]
# numeric checks K
cA = (B1-A1)/(B1-1)
numlo = T0*(lA + cA) + lB - PLO*(A3-B1) - (B1-A1)*(PLO + 1/(B1**2+B1))
assert numlo > 0, numlo
cC = (B3h-A3h)/(B3h-1)
assert uC - cC > 0
numhi = T1*(uC - cC) + uD - PHI*(B3h-B1h) + (B3h-A3h)*(PHI + 1/(B3h**2+B3h))
assert numhi < 0, numhi
print('numlo', float(numlo), 'numhi', float(numhi))
consts = dict(T0=T0,T1=T1,PLO=PLO,PHI=PHI,A1=A1,B1=B1,A3=A3,B1h=B1h,A3h=A3h,B3h=B3h,lA=lA,lB=lB,uC=uC,uD=uD,X0=X0,X1=X1,S0=S0,S1=S1)
for k,v in consts.items(): print(k, lit(v))
# covers
def emit_cover(name, pts, piece, hyp_lo_strict, concl):
    """nested case split; piece lemma applied with a b."""
    lines=[]
    lo = pts[0]; hi = pts[-1]
    s = f"lemma {name} {{θ x : ℝ}} (hθ0 : {L(T0)} ≤ θ) (hθ1 : θ ≤ {L(T1)}) (h1 : {L(lo)} {'<' if hyp_lo_strict else '≤'} x) (h2 : x ≤ {L(hi)}) :\n    {concl} := by\n"
    for i in range(1, len(pts)):
        a, b = pts[i-1], pts[i]
        ap = f"(by linarith)"
        if i < len(pts)-1:
            s += f"  rcases le_or_gt x ({L(b)}) with c{i} | c{i}\n"
            s += f"  · exact {piece} hθ0 hθ1 (a := {L(a)}) (b := {L(b)}) (by norm_num) (by linarith) c{i} (by norm_num)\n"
        else:
            s += f"  exact {piece} hθ0 hθ1 (a := {L(a)}) (b := {L(b)}) (by norm_num) (by linarith) h2 (by norm_num)\n"
    return s
out.append(emit_cover('q_neg_L', P_qneg1, 'q_neg_piece', True, 'q θ x < 0'))
out.append(emit_cover('dq_pos_W1', P_d1, 'dq_pos_piece', False, '0 < dq θ x'))
out.append(emit_cover('q_pos_M', P_qpos, 'q_pos_piece', False, '0 < q θ x'))
out.append(emit_cover('dq_neg_W2', P_d2, 'dq_neg_piece', False, 'dq θ x < 0'))
out.append(emit_cover('q_neg_R', P_qneg2, 'q_neg_piece', False, 'q θ x < 0'))
open(f'{TAG}_certs.lean.txt','w').write("\n".join(out))

# ---------- ratio and acentric ----------
Ob = lambda x: x*x/3 - x - 1
RLO = PLO*AL0*(X0/9)/(Ob(X1)**2); RHI = PHI*AL1*(X1/9)/(Ob(X0)**2)
print('ratio', float(RLO), float(RHI))
RT = F(*VAR['ratio']); HW = F(1, 2*10**VAR['ratio_k'])
assert RT - HW < RLO and RHI < RT + HW
RLOr = F(math.floor(RLO*10**8), 10**8); RHIr = F(math.ceil(RHI*10**8), 10**8)
print('RLOr RHIr', lit(RLOr), lit(RHIr))
tE, lE = emit_log('logR_lo', f"{L(RLOr)}", RLOr, 'lo')
tF, uF = emit_log('logR_hi', f"{L(RHIr)}", RHIr, 'hi')
tG, lG = emit_log('log1000_lo', "(1000 : ℝ)", F(1000), 'lo')
tH, uH = emit_log('log1000_hi', "(1000 : ℝ)", F(1000), 'hi')
L10lo, L10hi = lG/3, uH/3
WT = F(*VAR['omega']); WH = F(1, 2*10**VAR['omega_k'])
ALO, AHI = -(1 + WT + WH), -(1 + WT - WH)
assert lE >= ALO*L10lo and uF <= AHI*L10hi
print('acentric margins', float(lE - ALO*L10lo), float(AHI*L10hi - uF))
open(f'{TAG}_certs2.lean.txt','w').write("\n".join([tE,tF,tG,tH]))
print('T0 check', float(F(7,10)*K0/AL1 - T0), float(T1 - F(7,10)*K1/AL0))
import json
json.dump({k: lit(v) for k, v in dict(T0=T0,T1=T1,PLO=PLO,PHI=PHI,A1=A1,B1=B1,A3=A3,B1h=B1h,A3h=A3h,B3h=B3h,lA=lA,lB=lB,uC=uC,uD=uD,X0=X0,X1=X1,S0=S0,S1=S1,RLOr=RLOr,RHIr=RHIr,W1a=W1a,W1b=W1b,W2a=W2a,W2b=W2b,XF=XF).items()}, open(f'{TAG}_consts.json','w'), indent=1)
