# Port of 0028Z A06 to the tagged records (run 0228Z): the same digit transposition, written as an
# author would now write it, with the certification tag of the number.
import sys, pathlib
p = pathlib.Path(sys.argv[1]) / "FINDINGS.md"; s = p.read_text(encoding="utf-8")
old = "instead of 3.115[✓F1_l0]"; assert s.count(old) == 1
p.write_text(s.replace(old, "instead of 3.151[✓F1_l0]"), encoding="utf-8")
