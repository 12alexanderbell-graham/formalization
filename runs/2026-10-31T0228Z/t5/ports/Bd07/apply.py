# Port of 0028Z B07 (run 0228Z): same wrong number, tag kept.
import sys, pathlib
p = pathlib.Path(sys.argv[1]) / "FINDINGS.md"; s = p.read_text(encoding="utf-8")
old = "−0.249[✓F10_eta]ε"; assert s.count(old) == 1
p.write_text(s.replace(old, "−0.149[✓F10_eta]ε"), encoding="utf-8")
