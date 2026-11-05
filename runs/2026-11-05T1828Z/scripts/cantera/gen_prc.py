"""Certificates for the Peng-Robinson omega = 1 window with the Cantera-coded 1978 kappa (run 2026-11-05T1828Z; adapted from run 1228Z). Exact rationals.
Reduced variables x = v/b, theta = R T b / a(T), pi = p b^2 / a(T); g = theta/(x-1) - 1/(x^2+2x-1);
psi = theta log(x-1) + (r/4)(log(x+1+r) - log(x+1-r)) - pi x with r = sqrt 2.
Writes prc_consts.json (numbers) and prc_certs.lean.txt (log lemmas and covers)."""
import json, math
from fractions import Fraction as F
from mpmath import mp, mpf, sqrt, findroot, polyroots, log
mp.dps = 50
def m(fr): return mpf(fr.numerator)/fr.denominator
def lit(fr): return f"{fr.numerator} / {fr.denominator}" if fr.denominator != 1 else f"{fr.numerator}"
L = lambda fr: '(' + lit(fr) + ')'
def rnd(fr, d, up):
    v = fr*10**d; n = math.ceil(v) if up else math.floor(v); return F(n, 10**d)
f = lambda x: x**3 - 3*x**2 - 3*x - 3
X0 = F(39513730, 10**7); X1 = F(39513731, 10**7)
assert f(X0) < 0 < f(X1)
S0 = F(836660026, 10**9); S1 = F(836660027, 10**9)
assert S0*S0 < F(7,10) < S1*S1
KAP = F(1714388, 1000000)
assert KAP == F(374642,1000000) + F(1487503,1000000) - F(164423,1000000) + F(16666,1000000)  # Cantera code coefficients
R0 = F(1414213562373, 10**12); R1 = F(1414213562374, 10**12)
assert R0*R0 < 2 < R1*R1
D = lambda x: x*x + 2*x - 1
N = lambda x: x*x - 2*x - 1
# crude theta_c bounds (numerator, denominator increasing in x on [X0, X1])
TC0 = (X0-1)**2*(2*X0+2)/D(X1)**2; TC1 = (X1-1)**2*(2*X1+2)/D(X0)**2
al = lambda s: (1 + KAP*(1-s))**2   # decreasing in s
T0 = rnd(F(7,10)*TC0/al(S0), 11, False); T1 = rnd(F(7,10)*TC1/al(S1), 11, True)
print('theta', float(T0), float(T1), float(T1-T0))
# q = (2x+2)(x-1)^2 - th D^2 ; dq = 2(x-1)(3x+1) - 4 th D (x+1)
qp = lambda x: (2*x+2)*(x-1)**2
qm = lambda x: D(x)**2
def qneg_ok(a,b): return qp(b) < T0*qm(a)
def qpos_ok(a,b): return qp(a) > T1*qm(b)
def dpos_ok(a,b): return 2*(a-1)*(3*a+1) > 4*T1*D(b)*(b+1)
def dneg_ok(a,b): return 2*(b-1)*(3*b+1) < 4*T0*D(a)*(a+1)
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
# spinodals for orientation
th = (m(T0)+m(T1))/2
for x0 in [1.5, 22]:
    print('spinodal', findroot(lambda x: (2*x+2)*(x-1)**2 - th*(x*x+2*x-1)**2, x0))
W1a, W1b, W2a, W2b, XF = F(7,5), F(17,10), F(19), F(25), F(30)
P_qneg1 = cover(F(1), W1a, qneg_ok, F(1,10))
P_d1 = cover(W1a, W1b, dpos_ok, F(1,10))
P_qpos = cover(W1b, W2a, qpos_ok, F(1))
P_d2 = cover(W2a, W2b, dneg_ok, F(1))
P_qneg2 = cover(W2b, XF, qneg_ok, F(1))
assert 2*XF + 2 < T0*XF**2
for n,p in [('qneg1',P_qneg1),('d1',P_d1),('qpos',P_qpos),('d2',P_d2),('qneg2',P_qneg2)]:
    print(n, len(p)-1)
def g(t,x): return t/(x-1) - 1/(x*x+2*x-1)
def roots(p,t):
    # p(x-1)D = t D - (x-1):  p x^3 + (p - t) x^2 + (-3p - 2t + 1) x + (p + t - 1) = 0
    return sorted([z.real for z in polyroots([p, p-t, -3*p-2*t+1, p+t-1], maxsteps=200, extraprec=80) if abs(z.imag) < mpf(10)**-30 and z.real > 1])
PLO = F(81140, 10**9); PHI = F(81175, 10**9)
def sigfig(v, up, d=7):
    s = 10**d; n = math.ceil(v*s) if up else math.floor(v*s); return F(int(n), s)
rl0 = roots(m(PLO), m(T0)); rl1 = roots(m(PLO), m(T1))
A1 = sigfig(min(rl0[0], rl1[0]), False); B1 = sigfig(max(rl0[0], rl1[0]), True)
A3 = sigfig(min(rl0[2], rl1[2]), False, 3)
assert g(T0,A1) > PLO and g(T1,B1) < PLO and g(T0,A3) > PLO
rh0 = roots(m(PHI), m(T0)); rh1 = roots(m(PHI), m(T1))
B1h = sigfig(max(rh0[0],rh1[0]), True)
A3h = sigfig(min(rh0[2],rh1[2]), False, 3); B3h = sigfig(max(rh0[2],rh1[2]), True, 3)
assert g(T1,B1h) < PHI and g(T0,A3h) > PHI and g(T1,B3h) < PHI
assert A1 < B1 < W1a and A3 > XF and B1h < W1a and A3h > XF and A3h < B3h
print('A1 B1 A3', A1, B1, A3, 'B1h A3h B3h', B1h, A3h, B3h)

LOG2LO = F(6931471803, 10**10); LOG2HI = F(6931471808, 10**10)
def logcert(r):
    lr = log(m(r)); k = int(round(float(lr/log(2))))
    t = 1 - m(r)/mpf(2)**k
    t0 = F(int(round(float(t)*10**5)), 10**5)
    y = r / (F(2)**k * (1 - t0))
    at = abs(t0); n = 1
    while at**(n+1)/(1-at) > F(1, 10**13): n += 1
    S = sum(t0**(i+1)/(i+1) for i in range(n)); E = at**(n+1)/(1-at)
    if k >= 0: l2lo, l2hi = k*LOG2LO, k*LOG2HI
    else: l2lo, l2hi = k*LOG2HI, k*LOG2LO
    lo = l2lo - S - E + (1 - 1/y); hi = l2hi - S + E + (y - 1)
    lo = F(math.floor(lo*10**13), 10**13); hi = F(math.ceil(hi*10**13), 10**13)
    assert m(lo) < lr < m(hi) and lo < hi
    return k, t0, y, n, lo, hi
def emit_log(name, rexpr, r, want):
    k,t0,y,n,lo,hi = logcert(r)
    concl = f"{lit(lo)} < Real.log ({rexpr})" if want=='lo' else f"Real.log ({rexpr}) < {lit(hi)}"
    if k >= 0:
        fac = f"(2:ℝ) ^ {k} * (1 - ({lit(t0)})) * ({lit(y)})"
        rw = "Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_pow"
    else:
        fac = f"(1 - ({lit(t0)})) / (2:ℝ) ^ {-k} * ({lit(y*F(2)**k*F(2)**(-k))})"
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
# K_lo: theta*(L1 + cA) + (r/4) M - PLO (A3 - B1) - (B1 - A1)(PLO + 1/D(B1)) > 0
rA = (A3-1)/(B1-1)
QA = (A3+1+R0)*(B1+1-R1)/((A3+1-R0)*(B1+1+R1))   # M >= log QA
tA, lA = emit_log('logA_lo', f"({L(A3)} - 1) / ({L(B1)} - 1)", rA, 'lo')
tQA, lQA = emit_log('logQA_lo', f"({L(A3)} + 1 + {L(R0)}) * ({L(B1)} + 1 - {L(R1)}) / (({L(A3)} + 1 - {L(R0)}) * ({L(B1)} + 1 + {L(R1)}))", QA, 'lo')
assert lQA < 0
cA = (B1-A1)/(B1-1)
numlo = T0*(lA + cA) + R1/4*lQA - PLO*(A3-B1) - (B1-A1)*(PLO + 1/D(B1))
assert lA + cA > 0
print('numlo', float(numlo)); assert numlo > 0
# K_hi: theta*(L1 - cC) + (r/4) M - PHI (B3h - B1h) + (B3h - A3h)(PHI + 1/D(B3h)) < 0
rC = (B3h-1)/(B1h-1)
QC = (B3h+1+R1)*(B1h+1-R0)/((B3h+1-R1)*(B1h+1+R0))  # M <= log QC
tC, uC = emit_log('logC_hi', f"({L(B3h)} - 1) / ({L(B1h)} - 1)", rC, 'hi')
tQC, uQC = emit_log('logQC_hi', f"({L(B3h)} + 1 + {L(R1)}) * ({L(B1h)} + 1 - {L(R0)}) / (({L(B3h)} + 1 - {L(R1)}) * ({L(B1h)} + 1 + {L(R0)}))", QC, 'hi')
assert uQC < 0
cC = (B3h-A3h)/(B3h-1)
assert uC - cC > 0
numhi = T1*(uC - cC) + R0/4*uQC - PHI*(B3h-B1h) + (B3h-A3h)*(PHI + 1/D(B3h))
print('numhi', float(numhi)); assert numhi < 0
out += [tA, tQA, tC, tQC]
def emit_cover(name, pts, piece, strict, concl):
    lo = pts[0]; hi = pts[-1]
    s = f"lemma {name} {{θ x : ℝ}} (hθ0 : {L(T0)} ≤ θ) (hθ1 : θ ≤ {L(T1)}) (h1 : {L(lo)} {'<' if strict else '≤'} x) (h2 : x ≤ {L(hi)}) :\n    {concl} := by\n"
    for i in range(1, len(pts)):
        a, b = pts[i-1], pts[i]
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
open('prc_certs.lean.txt','w').write("\n".join(out))
# ratio ps/Pc = pi * alpha * D(x)^2 / N(x)  (x = x_c); D^2/N increasing? check at both ends
rat = lambda x: D(x)**2/N(x)
RA0 = min(rat(X0), rat(X1)); RA1 = max(rat(X0), rat(X1))
# crude: D^2 increasing, N increasing: D(X0)^2/N(X1) <= D^2/N <= D(X1)^2/N(X0)
RA0 = D(X0)**2/N(X1); RA1 = D(X1)**2/N(X0)
RLO = PLO*al(S1)*RA0; RHI = PHI*al(S0)*RA1
print('ratio', float(RLO), float(RHI))
RLOr = rnd(RLO, 10, False); RHIr = rnd(RHI, 10, True)
tE, lE = emit_log('logR_lo', f"{L(RLOr)}", RLOr, 'lo')
tF, uF = emit_log('logR_hi', f"{L(RHIr)}", RHIr, 'hi')
tG, lG = emit_log('log1000_lo', "(1000 : ℝ)", F(1000), 'lo')
tH, uH = emit_log('log1000_hi', "(1000 : ℝ)", F(1000), 'hi')
L10lo, L10hi = lG/3, uH/3
# omega in [0.9975, 0.9985] <=> log10 r in [-1.9985, -1.9975]
assert lE >= -F(19985,10**4)*L10lo and uF <= -F(19975,10**4)*L10hi, (float(lE + F(19985,10**4)*L10lo), float(-F(19975,10**4)*L10hi - uF))
print('acentric margins', float(lE + F(19985,10**4)*L10lo), float(-F(19975,10**4)*L10hi - uF))
assert F(95,10**4) <= RLOr and RHIr <= F(105,10**4)
open('prc_certs2.lean.txt','w').write("\n".join([tE,tF,tG,tH]))
consts = dict(T0=T0,T1=T1,PLO=PLO,PHI=PHI,A1=A1,B1=B1,A3=A3,B1h=B1h,A3h=A3h,B3h=B3h,lA=lA,lQA=lQA,uC=uC,uQC=uQC,
              X0=X0,X1=X1,S0=S0,S1=S1,R0=R0,R1=R1,W1a=W1a,W1b=W1b,W2a=W2a,W2b=W2b,XF=XF,RLOr=RLOr,RHIr=RHIr)
json.dump({k: lit(v) for k,v in consts.items()}, open('prc_consts.json','w'), indent=1)
for k,v in consts.items(): print(k, lit(v))
