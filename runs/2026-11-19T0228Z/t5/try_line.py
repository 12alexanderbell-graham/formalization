#!/usr/bin/env python3
"""Run 2026-11-19T0228Z (red team M4 harness): insert LINE into FILE of the working tree (STATE.md: directly under the
heading whose text contains --under TEXT, default the Gelfand multiplicity heading; other files: appended at the end,
or for a run README inserted after its first line) and run check_headline_mentions' rule set on the new line.
Usage: try_line.py FILE LINE [--under TEXT]    -> PASS (the line is accepted) or FLAGGED with the findings."""
import sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / "scripts/trust"))
import check_headline_mentions as C

args = sys.argv[1:]
under = "## Mathematics: multiplicity of radial solutions of the Gelfand problem"
if "--under" in args:
    k = args.index("--under"); under = args[k + 1]; del args[k:k + 2]
f, line = args[0], " ".join(args[1:])
head = C.files_at(None)
if f not in head:
    head[f] = (ROOT / f).read_text(encoding="utf-8") if (ROOT / f).exists() else "# Run\n"
txt = head[f]
if f == "STATE.md":
    i = next(i for i, l in enumerate(txt.splitlines(keepends=True)) if l.startswith("#") and under in l)
    ls = txt.splitlines(keepends=True); ls.insert(i + 1, line + "\n"); new_txt = "".join(ls)
elif C.RUN_README.match(f):
    ls = txt.splitlines(keepends=True); ls.insert(1, "\n" + line + "\n"); new_txt = "".join(ls)
else:
    new_txt = txt.rstrip("\n") + "\n\n" + line + "\n"
new = dict(head); new[f] = new_txt
base = dict(C.files_at(None))
e = C.run(base, new)
print("PASS (accepted)" if not e else "FLAGGED:\n  " + "\n  ".join(e))
