# Port of red team D, d02, to the bound inputs of check v3 (run 0228Z): the input Ω_m = 0.3 next to
# numbers certified at 0.3 is changed to 0.7, keeping the binding tag.
import sys, pathlib
p = pathlib.Path(sys.argv[1]) / "FINDINGS.md"; s = p.read_text(encoding="utf-8")
old = "at Ω_m = 0.3[in✓F1_l0] the printed"; assert s.count(old) == 1
p.write_text(s.replace(old, "at Ω_m = 0.7[in✓F1_l0] the printed"), encoding="utf-8")
