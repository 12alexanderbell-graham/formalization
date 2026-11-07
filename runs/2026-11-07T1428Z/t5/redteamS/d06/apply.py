#!/usr/bin/env python3
"""d06: FINDINGS.md F3, bullet "Second misprint in the same appendix (sympy + typeset, NOT in Lean)": the status is
upgraded to "(sympy + typeset + Lean)" and a sentence says that Checked.Cosmography.CCS.lookback_fifth_order
machine-checks (A5) and the printed curvature terms together with (A2). That theorem is the flat lookback series to
z^5 (a scale factor, no curvature constant, no R^5_D): it covers neither claim. The sentence has no decimal, so
check_numbers has nothing to tag; the cited name is a registered headline, so precheck_citations passes; no script
compares FINDINGS prose with the Lean evidence it cites. usage: apply.py <repo_root>"""
import sys
from pathlib import Path

root = Path(sys.argv[1])
p = root / "FINDINGS.md"
t = p.read_text(encoding="utf-8")
old1 = "**Second misprint in the same appendix (sympy + typeset, NOT in Lean):**"
new1 = "**Second misprint in the same appendix (sympy + typeset + Lean):**"
old2 = "(each lacks a +K²/120, K = kc²/(a₀²H₀²)); the paper's analysis is flat."
new2 = ("(each lacks a +K²/120, K = kc²/(a₀²H₀²)); the paper's analysis is flat. Lean evidence (Checked): "
        "`Checked.Cosmography.CCS.lookback_fifth_order` fixes every coefficient of the fifth-order lookback series, so "
        "(A5) and the printed curvature terms are machine-checked together with (A2) (`printedD4_fails`, "
        "`printedD4_fails_past`).")
for o in (old1, old2):
    assert t.count(o) == 1, (o, t.count(o))
p.write_text(t.replace(old1, new1).replace(old2, new2), encoding="utf-8")
print("d06 applied")
