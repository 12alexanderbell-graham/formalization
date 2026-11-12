import os, textwrap
APPLY = '''#!/usr/bin/env python3
import sys, pathlib
root = pathlib.Path(sys.argv[1])
LEAN = r"""@@LEAN@@"""
mod = "@@MOD@@"
(root / "Checked" / "Trust" / (mod + ".lean")).write_text(LEAN)
p = root / "Checked.lean"
s = p.read_text()
assert ("import Checked.Trust." + mod + "\\n") not in s
if not s.endswith("\\n"): s += "\\n"
p.write_text(s + "import Checked.Trust." + mod + "\\n")
h = root / "scripts" / "trust" / "headlines.txt"
s = h.read_text()
if not s.endswith("\\n"): s += "\\n"
assert "@@HEAD@@\\n" not in s
h.write_text(s + "@@HEAD@@\\n")
'''
def emit(n, mod, head, lean, claim):
    d = f"/home/claude/t5AH/d{n:02d}"
    os.makedirs(d, exist_ok=True)
    a = APPLY.replace("@@LEAN@@", lean).replace("@@MOD@@", mod).replace("@@HEAD@@", head)
    open(d + "/apply.py", "w").write(a)
    open(d + "/claim.md", "w").write(claim)

exec(open("/home/claude/t5AH/defs.py").read())
