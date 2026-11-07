#!/usr/bin/env python3
"""Status lines in STATE.md name what carries the status (run 2026-11-06T2228Z, part 3; written AFTER reading blind
red team P's report — not blind). Blocking in CI; pure Python.

Why: red team P d06 rewrote the STATE.md "Results" bullet of a Work-only theorem from "PROVED in Work + AUDITED"
to "PROVED (… promoted to Checked, CI green on every job, non-vacuity witnessed …)" while still citing only the
`Work.` name; no script read STATE.md beyond backticked `Checked.` citations. By annex XXXVIII, PROVED means green
CI on `Checked` + standard axioms + AUDITED: a bare PROVED is a claim about a Checked headline, so it must name one.

S1: a bullet of STATE.md whose leading bold status says PROVED, checked, promoted, verified, certified or CI green
    (since Q d01; before: begins with PROVED) and does not say "in Work" (e.g. "**PROVED**",
    "**PROVED once CI is green**") cites at least one backticked full name `Checked.…` that is a registered headline, or an existing module path
    `Checked/….lean`,
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
        # any leading bold status that claims a check (since blind red team Q d01: "**Machine-checked, promoted to
        # Checked and AUDITED**" over Work-only names avoided the PROVED shape)
        m = re.match(r"\s*[-*]\s+\*\*([^*]*(?:PROVED|[Cc]hecked|[Pp]romot|[Vv]erified|[Cc]ertified|CI\s+green)[^*]*)\*\*", line)
        if not m:
            continue
        status = m.group(1)
        names = re.findall(r"`((?:Checked|Work)\.[A-Za-z0-9_.']+)`", line)
        if re.search(r"\bin\s+Work\b", status):
            continue
        checked = [n for n in names if n.startswith("Checked.")]
        paths = [q for q in re.findall(r"`(Checked/[A-Za-z0-9_/]+\.lean)`", line) if (ROOT / q).exists()]
        if not checked and not paths:
            errors.append(f"S1: STATE.md:{i}: status '{status}' (PROVED means a Checked headline with green CI) cites no "
                          f"`Checked.…` headline or `Checked/…` module" + (f"; it cites {names[0]}" if names else ""))
            continue
        if names and names[0].startswith("Work.") and line.find("`" + names[0]) < min(
                [line.find(x) for x in ["`Checked." , "`Checked/"] if line.find(x) >= 0] or [len(line)]):
            errors.append(f"S1: STATE.md:{i}: status '{status}' cites {names[0]} before any Checked headline or module")
        if checked and not paths and not any(n == h or n.endswith("." + h) for n in checked for h in heads):
            errors.append(f"S1: STATE.md:{i}: status '{status}': none of {', '.join(checked)} is a registered headline")
    for e in errors:
        print("  " + e)
    print(f"check_status_lines: {'FAIL' if errors else 'ok'}")
    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main())
