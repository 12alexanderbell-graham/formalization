# Emits the Lean step-sum bounds for rl19_box_unmatched_h12 from gen_h12.py's exact grid (n = 8).
import subprocess, sys
sys.argv = ['gen_h12.py', '8']
src = open('gen_h12.py').read().split("n = int(sys.argv[1])")[0]
ns = {}
exec(src, ns)
F = ns['F']
def fmt(x):
    x = F(x)
    return f"({x.numerator} / {x.denominator} : ℝ)" if x.denominator != 1 else f"({x.numerator} : ℝ)"
def chain(kind, pts, cs, m):
    # right-nested split terms
    lem = 'fpiece_lo' if kind == 'lo' else 'fpiece_up'
    spl = 'fsplit_lo' if kind == 'lo' else 'fsplit_up'
    def piece(i):
        return f"({lem} {fmt(m)} {fmt(pts[i])} {fmt(pts[i+1])} {fmt(cs[i])} (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold yC; norm_num))"
    def rec(i):
        if i == len(cs) - 1: return piece(i)
        return f"({spl} {fmt(m)} (by norm_num) (by norm_num) {fmt(pts[i])} {fmt(pts[i+1])} 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) {piece(i)} {rec(i+1)})"
    return rec(0)
P1 = ns['pieces'](ns['w1'][0], ns['w1'][1], 8); P3 = ns['pieces'](ns['w3'][0], ns['w3'][1], 8)
m = ns['m']
out = []
for name, P in [('1', P1), ('3', P3)]:
    lo_sum = sum((q - p) * c for p, q, c in zip(P[0], P[0][1:], P[1]))
    up_sum = sum((q - p) * c for p, q, c in zip(P[2], P[2][1:], P[3]))
    out.append(f"theorem fJ{name}_lo : {fmt(lo_sum)} ≤ ∫ v in {fmt(P[0][0])}..1, gC {fmt(m)} 0 v := by\n  have h := {chain('lo', P[0], P[1], m)}\n  norm_num at h ⊢; linarith\n")
    out.append(f"theorem fJ{name}_up : ∫ v in {fmt(P[2][0])}..1, gC {fmt(m)} 0 v ≤ {fmt(up_sum)} := by\n  have h := {chain('up', P[2], P[3], m)}\n  norm_num at h ⊢; linarith\n")
    print(name, float(lo_sum), float(up_sum), file=sys.stderr)
open('../lean/h12_gen.lean', 'w').write('\n'.join(out))
