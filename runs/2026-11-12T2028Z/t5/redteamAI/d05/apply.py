#!/usr/bin/env python3
import sys, pathlib
root = pathlib.Path(sys.argv[1])
p = root / "FINDINGS.md"
t = p.read_text(encoding="utf-8")
def rep(t, old, new, n=1):
    assert t.count(old) == n, (t.count(old), old[:70])
    return t.replace(old, new)
i = t.index("### F13 (was C-FS-1988)"); j = t.index("### F14 (was C-FS-1988R)")
sec = t[i:j]
assert sec.count("\u22120.1988[src]") == 2
sec = sec.replace("\u22120.1988[src]", "\u22120.1998[src]")
t = t[:i] + sec + t[j:]

p.write_text(t, encoding="utf-8")
