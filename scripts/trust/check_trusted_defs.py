#!/usr/bin/env python3
"""Pin claims in TRUSTED_DEFINITIONS.md must match the pin registry (run 2026-11-04T0428Z). Blocking in CI.

TRUSTED_DEFINITIONS.md is prose that scientists read next to TRUST_MAP.md. Red team F (defect F08)
added a table row claiming that `cubicP`, `critCubic` and `acentric` are pinned by the Maxwell and
critical-point specs; no script read the file, so the false claim passed. This script reads the T1
table (the first table of the file, column "Pinned?") and fails when a row says "yes" (pinned) for
a definition that `scripts/trust/pins.txt` does not pin, or names as its pin a `*_pins` theorem that
pins.txt does not list. It also fails when any other line of the file says a backticked program
definition "is pinned"/"are pinned" and pins.txt does not pin it.
"""
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]


def main():
    pins = []
    for l in (ROOT / "scripts/trust/pins.txt").read_text().splitlines():
        if l.strip() and not l.startswith("#"):
            d, t = l.split()
            pins.append((d, t))
    pdefs = [d for d, _ in pins]
    pthms = [t for _, t in pins]

    def same(a, b):
        """one dotted name is a dotted suffix of the other (`decelSpec_pins` vs `Fidelity.decelSpec_pins`)"""
        return a == b or a.endswith("." + b) or b.endswith("." + a)

    def is_pinned_def(name):
        return any(same(d, name) for d in pdefs)

    def is_pin_thm(name):
        return any(same(t, name) for t in pthms)

    text = (ROOT / "TRUSTED_DEFINITIONS.md").read_text(encoding="utf-8")
    errs = []
    lines = text.splitlines()
    # the T1 table: rows "| defs | spec | yes/no ... |" before the first blank line after its header
    in_t1 = False
    for i, l in enumerate(lines):
        if l.startswith("| Definition | Spec |"):
            in_t1 = True
            continue
        if in_t1 and not l.startswith("|"):
            in_t1 = False
        if in_t1 and l.startswith("|") and not l.startswith("|---"):
            cells = [c.strip() for c in l.strip().strip("|").split("|")]
            if len(cells) < 3:
                continue
            if re.match(r"(?i)yes\b", cells[2]):
                for d in re.findall(r"`([A-Za-z_][\w.']*)`", cells[0]):
                    if not is_pinned_def(d):
                        errs.append(f"line {i+1}: says `{d}` is pinned, but scripts/trust/pins.txt pins no such definition")
                for t in re.findall(r"`?([A-Za-z_][\w.']*_pins)\b", cells[2]):
                    if not is_pin_thm(t):
                        errs.append(f"line {i+1}: names `{t}` as a pin, but scripts/trust/pins.txt lists no such pin theorem")
    for i, l in enumerate(lines):
        for m in re.finditer(r"`([A-Za-z_][\w.']*)`[^.|;]*?\b(?:is|are) (?:now )?pinned\b", l):
            if not is_pinned_def(m.group(1)):
                errs.append(f"line {i+1}: says `{m.group(1)}` is pinned, but scripts/trust/pins.txt pins no such definition")
    # run 2026-11-04T1028Z (red team G: d04 added rows claiming the Michaelis–Menten predicate covers
    # product rebinding and every rate constant, d07 widened the domain of the `decel` pin to turnaround
    # points; the pin names were right, so the pin-claim rules above passed): with --base, every added
    # or changed line of TRUSTED_DEFINITIONS.md must be disclosed by a LEDGER.md addition of the same
    # push that names a backticked constant of that line (or the file, for lines naming none)
    if "--base" in sys.argv:
        import subprocess
        b = sys.argv[sys.argv.index("--base") + 1]
        r = subprocess.run(["git", "show", f"{b}:TRUSTED_DEFINITIONS.md"], cwd=ROOT, capture_output=True, text=True)
        if r.returncode == 0:
            old = set(r.stdout.splitlines())
            d = subprocess.run(["git", "diff", b, "HEAD", "--", "LEDGER.md"], cwd=ROOT, capture_output=True, text=True)
            added = "\n".join(x for x in d.stdout.splitlines() if x.startswith("+"))
            for i, l in enumerate(lines):
                if l.strip() and l not in old:
                    names = [n.split(".")[-1] for n in re.findall(r"`([A-Za-z_][\w.']*)`", l)]
                    ok = any(n in added for n in names) if names else "TRUSTED_DEFINITIONS.md" in added
                    if not ok:
                        errs.append(f"line {i+1}: new or changed since {b} and not disclosed: a LEDGER.md addition must name "
                                    f"{', '.join('`' + n + '`' for n in names) if names else 'TRUSTED_DEFINITIONS.md'} "
                                    f"(the prose of this file is what a scientist reads about each definition)")
    print(f"check_trusted_defs: {len(pins)} pins; {len(errs)} problems in TRUSTED_DEFINITIONS.md")
    for e in errs:
        print("::error::" + e)
    return 1 if errs else 0


if __name__ == "__main__":
    sys.exit(main())
