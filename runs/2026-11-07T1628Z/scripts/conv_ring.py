#!/usr/bin/env python3
"""Run 2026-11-07T1628Z: replace the per-cell `ring` proofs of the defect identities in the generated
Duffing, Michaelis–Menten and Robertson certificate modules by kernel evaluation
(`Checked.Sim.QResid`, `Checked.Sim.QResidRob`). Statements, data and every other proof step are
left byte-identical; the script asserts that no `ring` remains and that the theorem headers are unchanged.

Usage: conv_ring.py <file.lean> ...   (rewrites in place)
"""
import re, sys

SHOW = re.compile(r"rw \[show (?P<lhs>[^\n]*?)\s*=\s*evalQ (?P<d>\w+) (?P<arg>\([^\n]*?\)|\w+) by\s+"
                  r"simp only \[(?P<names>[^\]]*)\]; push_cast; ring\]")
SUM = re.compile(r"(?P<head>have hsum : evalQ (?P<a>\w+) [^\n]*? = evalQ (?P<d>\w+) [^\n]*?) := by\s+"
                 r"simp only \[[^\]]*\]; push_cast; ring")

def classify(lhs, d, arg):
    m = re.fullmatch(r"dEvalQ (\w+) (\w+) - evalQ (\w+) \2", lhs)
    if m: return f"duf_a {m[1]} {m[3]} {d} (by decide +kernel) {m[2]}"
    m = re.fullmatch(r"dEvalQ (\w+) (\w+) \+ evalQ (\w+) \2 \+ evalQ \3 \2 \^ 3", lhs)
    if m: return f"duf_b {m[3]} {m[1]} {d} (by decide +kernel) {m[2]}"
    m = re.fullmatch(r"dEvalQ (\w+) (\S+) - \(-evalQ \1 \2 \+ evalQ (\w+) \2 \* evalQ \1 \2 \+ evalQ \3 \2\)", lhs)
    if m: return f"mm_a {m[1]} {m[3]} {d} (by decide +kernel) {m[2]}"
    m = re.fullmatch(r"dEvalQ (\w+) (\S+) - \(evalQ (\w+) \2 - evalQ \1 \2 \* evalQ \3 \2 - 2 \* evalQ \1 \2\)", lhs)
    if m: return f"mm_b {m[3]} {m[1]} {d} (by decide +kernel) {m[2]}"
    m = re.fullmatch(r"dEvalQ (\w+) (\w+) - rob([PQ]) \(evalQ (\w+) \2\) \(evalQ (\w+) \2\)", lhs)
    if m:
        p, var, which, p2, p3 = m[1], m[2], m[3], m[4], m[5]
        assert p == (p2 if which == "P" else p3), lhs
        lem = "rob_a" if which == "P" else "rob_b"
        if arg == var:
            return f"{lem} {p2} {p3} {d} (by decide +kernel) {var}"
        s = re.fullmatch(r"\(" + re.escape(var) + r" / \(([^:]+) : ℝ\)\)", arg)
        assert s, arg
        r = s[1].strip()
        return f"{lem}_s {p2} {p3} {d} ({r}) (by norm_num) (by norm_num) (by decide +kernel) {var}"
    raise SystemExit(f"unrecognised defect identity: {lhs}")

def headers(t):
    return re.findall(r"^theorem[^\n]*(?:\n    [^\n]*)*?:= by", t, re.M)

for path in sys.argv[1:]:
    t = open(path, encoding="utf-8").read()
    n0 = len(SHOW.findall(t)) + len(SUM.findall(t))
    def rep(m):
        return f"rw [show {m['lhs']} = evalQ {m['d']} {m['arg']} from {classify(m['lhs'], m['d'], m['arg'])}]"
    u = SHOW.sub(rep, t)
    u = SUM.sub(lambda m: f"{m['head']} :=\n      mm_sum {m['a']} {m['a'].replace('ps', 'pc')} {m['d']} (by decide +kernel) _", u)
    assert not re.search(r"\bring\b", u), f"{path}: ring left"
    assert headers(t) == headers(u), f"{path}: a theorem header changed"
    imp = "import Checked.Sim.QResidRob" if "rob" in u else "import Checked.Sim.QResid"
    lines = u.split("\n")
    last_imp = max(i for i, l in enumerate(lines) if l.startswith("import "))
    lines.insert(last_imp + 1, imp)
    u = "\n".join(lines)
    opens = " Checked.Sim.QResid" + (" Checked.Sim.QResidRob" if "rob" in imp.lower() else "")
    u, k = re.subn(r"^(open [^\n]*)$", lambda m: m[1] + opens, u, count=1, flags=re.M)
    assert k == 1
    open(path, "w", encoding="utf-8").write(u)
    print(f"{path}: {n0} identities converted")
