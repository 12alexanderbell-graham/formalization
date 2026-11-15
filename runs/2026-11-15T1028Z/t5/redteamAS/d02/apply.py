import sys; sys.path.insert(0, "/home/claude/t5AS")
from common import *
R = root()
old = "Protocol before any of these becomes a finding (original XXVIII.1, XXIX; annex 47.2):"
new = ("Every finding in the verified section above passed this whole protocol: each printed value in it was read a second time, blind, "
       "from the journal's own typeset page (never from arXiv text or a summary), and each is certified in Lean for all parameter values of its model, not at single points. "
       "Protocol before any of these becomes a finding (original XXVIII.1, XXIX; annex 47.2):")
edit(R, old, new)
ledger(R, "- Run 2026-11-15T1028Z: FINDINGS.md candidates-section introduction reworded (protocol sentence); no verified section touched.")
regen(R)
