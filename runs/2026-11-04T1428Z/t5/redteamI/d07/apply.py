import sys, os
root = sys.argv[1]
def rd(p):
    return open(os.path.join(root, p), encoding="utf-8").read()
def wr(p, s):
    open(os.path.join(root, p), "w", encoding="utf-8").write(s)
def rep(p, old, new):
    s = rd(p); assert s.count(old) == 1, (p, old[:40], s.count(old)); wr(p, s.replace(old, new))
def app(p, add):
    s = rd(p); wr(p, s + add)

rep("CHANGELOG.md", "printed D⁴ refuted in every model with q₀ ≠ 0 (two-sided and past-only). Blind restatement closed in Lean; referee STANDS.",
    "printed D⁴ refuted in every model (two-sided and past-only), including q₀ = 0 and the non-accelerating Milne universe. Blind restatement closed in Lean; referee STANDS.")
