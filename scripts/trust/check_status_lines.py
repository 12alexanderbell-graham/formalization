#!/usr/bin/env python3
"""Status lines in STATE.md name what carries the status (run 2026-11-06T2228Z, part 3; written AFTER reading blind
red team P's report — not blind). Blocking in CI; pure Python.

Why: red team P d06 rewrote the STATE.md "Results" bullet of a Work-only theorem from "PROVED in Work + AUDITED"
to "PROVED (… promoted to Checked, CI green on every job, non-vacuity witnessed …)" while still citing only the
`Work.` name; no script read STATE.md beyond backticked `Checked.` citations. By annex XXXVIII, PROVED means green
CI on `Checked` + standard axioms + AUDITED: a bare PROVED is a claim about a Checked headline, so it must name one.

S1: a bullet of STATE.md whose bold status begins with PROVED and does not say "in Work" (e.g. "**PROVED**",
    "**PROVED once CI is green**") cites at least one backticked full name `Checked.…` that is a registered headline
    (`scripts/trust/headlines.txt`, entries are unique suffixes), and cites no backticked `Work.…` name before its
    first `Checked.…` name.

Limits: words outside the bold status (a bullet can still say "CI green" falsely: the CI run ID it cites is the
evidence a reader can follow), other files (README.md, run records), statuses other than PROVED.
"""
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]


def main():
    heads = {l.strip() for l in (ROOT / "scripts/trust/headlines.txt").read_text(encoding="utf-8").splitlines()
             if l.strip() and not l.startswith("#")}
    errors = []
    for i, line in enumerate((ROOT / "STATE.md").read_text(encoding="utf-8").splitlines(), 1):
        m = re.match(r"\s*[-*]\s+\*\*(PROVED[^*]*)\*\*", line)
        if not m:
            continue
        status = m.group(1)
        names = re.findall(r"`((?:Checked|Work)\.[A-Za-z0-9_.']+)`", line)
        if re.search(r"\bin\s+Work\b", status):
            continue
        checked = [n for n in names if n.startswith("Checked.")]
        if not checked:
            errors.append(f"S1: STATE.md:{i}: status '{status}' (PROVED means a Checked headline with green CI) cites no "
                          f"`Checked.…` headline" + (f"; it cites {names[0]}" if names else ""))
            continue
        if names[0].startswith("Work."):
            errors.append(f"S1: STATE.md:{i}: status '{status}' cites {names[0]} before any Checked headline")
        if not any(n == h or n.endswith("." + h) for n in checked for h in heads):
            errors.append(f"S1: STATE.md:{i}: status '{status}': none of {', '.join(checked)} is a registered headline")
    for e in errors:
        print("  " + e)
    print(f"check_status_lines: {'FAIL' if errors else 'ok'}")
    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main())
