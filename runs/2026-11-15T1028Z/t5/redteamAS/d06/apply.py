import sys, re; sys.path.insert(0, "/home/claude/t5AS")
from common import *
R = root()
t = (R/"FINDINGS.md").read_text()
m = re.search(r"^### (F2) — generated heading \(do not edit\): (.*)$", t, re.M)
head = "F2 — generated heading (do not edit): " + m.group(2)
slug = re.sub(r"[^\w\- ]", "", head.lower()).replace(" ", "-")
row = ("| C34 | Capozziello, Lazkoz, Salzano 2011, Eq. (22) | l₀ with a free CPL parameter | "
       f"[certified in Lean for all w₀, wₐ and Ω together](#{slug}) |\n")
edit(R, LAST, LAST + row)
ledger(R, "- Run 2026-11-15T1028Z: FINDINGS.md candidates table, new row C34 (link to the CPL entry); verified section untouched.")
regen(R)
