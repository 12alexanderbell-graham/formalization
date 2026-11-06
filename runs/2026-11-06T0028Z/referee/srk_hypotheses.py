"""Referee: what each hypothesis of srk_omega1_unique blocks (reduced units b = 1, R*Tc from the
critical point; P in units of Pc). Lean junk conventions: x/0 = 0; deriv of a non-differentiable
function = 0; the interval integral of a non-integrable function = 0.
(1) hl (b < vl): search for Maxwell states with vl < b. Any vl < vg straddling a pole (v = -b, 0, b)
    has integral 0 (non-integrable), so needs ps = 0 and P(vl) = P(vg) = 0. Otherwise vl, vg lie in one
    continuity interval (-inf,-b), (-b,0), (0,b) and a Maxwell state there needs 3 roots of P = ps in it.
    We list, over a wide scan of ps, how many roots of the cubic fall in each interval.
(2) hb (0 < b): b = -1, vc = 0 (pole of a/(v^2+bv)): deriv junk 0 twice, so IsCriticalIsotherm holds;
    explicit Maxwell state with ps = 0 straddling poles."""
from mpmath import mp, mpf, sqrt, cbrt, polyroots, re, im, log
mp.dps = 40
c = cbrt(2) - 1
Oa, Ob = 1/(9*c), c/3
kap = mpf('0.480') + mpf('1.574') - mpf('0.176')
alpha = (1 + kap*(1 - sqrt(mpf(7)/10)))**2
# reduced: b = 1, Pc = 1, R Tc = Pc b / Ob = 1/Ob, a_c = Oa (R Tc)^2 / Pc
RTc = 1/Ob; ac = Oa*RTc**2; RT = mpf(7)/10*RTc; a = ac*alpha
P = lambda v: RT/(v - 1) - a/(v*v + v)
def roots(p):  # p (v-1) v (v+1) - RT v (v+1) + a (v-1) = 0
    cc = [p, -RT, -p - RT + a, -a]
    while cc[0] == 0: cc = cc[1:]
    return sorted(re(r) for r in polyroots(cc, maxsteps=400, extraprec=400) if abs(im(r)) < mpf(10)**-25)
F = lambda v: RT*log(abs(v - 1)) - a*log(abs(v/(v + 1)))   # antiderivative on each continuity interval
print("P = 0 roots (v/b):", [mp.nstr(r, 10) for r in roots(mpf(0))], "(both > b, so no ps = 0 state can have vl < b)")
counts = {}
found = []
for k in range(-400, 401):
    for s in (1, -1):
        p = s*mpf(10)**(mpf(k)/40)
        rs = roots(p)
        key = tuple(sum(1 for r in rs if lo < r < hi) for lo, hi in [(-mp.inf, -1), (-1, 0), (0, 1), (1, mp.inf)])
        counts[key] = counts.get(key, 0) + 1
        for lo, hi in [(-mp.inf, -1), (-1, 0), (0, 1)]:
            ins = [r for r in rs if lo < r < hi]
            if len(ins) >= 2:
                for i in range(len(ins)):
                    for j in range(i + 1, len(ins)):
                        A = F(ins[j]) - F(ins[i]) - p*(ins[j] - ins[i])
                        found.append((p, ins[i], ins[j], A))
print("root counts per interval [(-inf,-b),(-b,0),(0,b),(b,inf)] over", 2*801, "levels |ps|/Pc in [1e-10,1e10]:", counts)
print("pairs of roots in one interval below b:", len(found),
      "; min |area residual| / (p (vg-vl)):", mp.nstr(min([abs(A/(p*(vj - vi))) for p, vi, vj, A in found], default=None), 5))
# (2) b < 0 junk
b = mpf(-1); R = mpf(1); Tc = mpf(1); acj = mpf(1); a7 = acj*alpha; T7 = mpf(7)/10
Pc = R*Tc/(0 - b) - 0   # cubicP at vc = 0: a/(0^2 + b*0) = a/0 = 0 in Lean
# P(v) = 0 at 0.7 Tc:  R T7 v (v + b) = a7 (v - b)  ->  R T7 v^2 + (R T7 b - a7) v + a7 b = 0
A2, B2, C2 = R*T7, R*T7*b - a7, a7*b
d = sqrt(B2**2 - 4*A2*C2); r1, r2 = (-B2 - d)/(2*A2), (-B2 + d)/(2*A2)
print("b<0 junk: Pc =", Pc, " vl =", mp.nstr(r1, 8), " vg =", mp.nstr(r2, 8), " (vl > b:", r1 > b, "; poles 0 and -b=1 inside (vl,vg))",
      " so integral = 0 = 0*(vg-vl), ps = 0, ps/Pc = 0, not 0.0102")
