import sys, re, os
def load(root):
    return open(os.path.join(root, "FINDINGS.md"), encoding="utf-8").read()
def save(root, t):
    open(os.path.join(root, "FINDINGS.md"), "w", encoding="utf-8").write(t)
def ledger(root, k, what):
    p = os.path.join(root, "LEDGER.md")
    s = open(p, encoding="utf-8").read().rstrip("\n")
    s += f"\n- 2026-11-14 — FINDINGS.md `{k}`: {what}\n"
    open(p, "w", encoding="utf-8").write(s)
def section(t, k):
    m = re.search(r"^### " + k + r"\b.*?(?=^### |^## )", t, re.S | re.M)
    return m.group(0)
