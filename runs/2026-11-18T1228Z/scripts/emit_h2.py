# Emits the Lean step bounds for fit_direction_h2 (Omega = 3/2) from gen_h2.py's exact grid (n = 8).
import sys
sys.argv = ['gen_h2.py', '8']
src = open('gen_h2.py').read().split("n = int(sys.argv[1])")[0]
ns = {}; exec(src, ns); F = ns['F']
def fmt(x):
    x = F(x)
    return f"({x.numerator} / {x.denominator} : ℝ)" if x.denominator != 1 else f"({x.numerator} : ℝ)"
O = ns['O']
def chain(kind, pts, cs):
    lem = 'piece_lo' if kind == 'lo' else 'piece_up'
    spl = 'gsplit_lo' if kind == 'lo' else 'gsplit_up'
    def piece(i):
        return f"({lem} {fmt(O)} {fmt(pts[i])} {fmt(pts[i+1])} {fmt(cs[i])} (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))"
    def rec(i):
        if i == len(cs) - 1: return piece(i)
        return f"({spl} {fmt(O)} (by norm_num) {fmt(pts[i])} {fmt(pts[i+1])} 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) {piece(i)} {rec(i+1)})"
    return rec(0)
out = []
for i in (1, 3, 5):
    lo = ns['lower'](ns['W'][i][1], 8); up = ns['upper'](ns['W'][i][0], 8)
    out.append(f"theorem gJ{i}_lo : {fmt(lo[2])} ≤ ∫ v in {fmt(lo[0][0])}..1, 2 / √({fmt(O)} + (1 - {fmt(O)}) * v ^ 6) := by\n  have h := {chain('lo', lo[0], lo[1])}\n  norm_num at h ⊢; linarith\n")
    out.append(f"theorem gJ{i}_up : ∫ v in {fmt(up[0][0])}..1, 2 / √({fmt(O)} + (1 - {fmt(O)}) * v ^ 6) ≤ {fmt(up[2])} := by\n  have h := {chain('up', up[0], up[1])}\n  norm_num at h ⊢; linarith\n")
    print(i, lo[2], up[2], file=sys.stderr)
open('../lean/h2_gen.lean', 'w').write('\n'.join(out))
