#!/usr/bin/env python3
"""Goal guard (run 2026-10-31, after Alexander: "better not lose that, you already lost it maybe thrice").

Fails CI if the program's goal and its "no narrowing" instruction disappear from the files every run
reads, or if a run record (from 2026-10-31T0100Z on) lacks its front-page line
`**THE RESULT:**` (which of the five parts of TARGETS "THE RESULT" the run moved, and how).
Changing this check is an integrity event (annex 39.5); weakening it needs Alexander.
"""
import pathlib, re, sys

root = pathlib.Path(__file__).resolve().parent.parent
errors = []

def need(path, *fragments, head=None):
    p = root / path
    if not p.exists():
        errors.append(f"{path}: missing")
        return
    text = p.read_text(encoding="utf-8")
    if head:
        text = "\n".join(text.splitlines()[:head])
    for f in fragments:
        if f not in text:
            where = f" (first {head} lines)" if head else ""
            errors.append(f"{path}{where}: missing required text: {f!r}")

need("PROMPT.md",
     "## THE GOAL AND THE RESULT",
     "allows scientists to trust AI to do scientific work without outside verification",
     "The result we are building and will publish is that goal achieved, in full",
     "stop narrowing shit down and deciding only part of something is possible",
     head=30)
need("TARGETS.md", "## THE RESULT")
need("governance/02_OPERATIVE_CORE.md", "**The result (Alexander, 2026-10-31):**")
need("STATE.md", "THE RESULT")
# reader-facing hand-written records say that they are unchecked (run 2026-11-04T1428Z; red team H,
# d07, put a false "general ODE solver, already cross-checked by experts" bullet into README.md, which no
# script reads): the banner may not be removed
UNCHECKED = "> **Unchecked prose.** This file is written by hand; no script checks what its sentences claim."
need("README.md", UNCHECKED, head=6)
need("STATE.md", UNCHECKED, head=6)

for readme in sorted((root / "runs").glob("*/README.md")):
    run_id = readme.parent.name
    if re.fullmatch(r"\d{4}-\d\d-\d\dT\d{4}Z", run_id) and run_id >= "2026-10-31T0100Z":
        if "**THE RESULT:**" not in readme.read_text(encoding="utf-8"):
            errors.append(f"runs/{run_id}/README.md: no '**THE RESULT:**' front-page line")

# a commit that says it removes the LOCK must remove it (run 2026-11-06T2228Z: records commit 1414e21 of run
# 2026-11-06T2028Z said "remove LOCK" but never staged the deletion, so the next run found a lock < 150 min old
# naming a finished run and had to judge from the commit message whether 48.4 applied)
import subprocess
try:
    head_msg = subprocess.run(["git", "log", "-1", "--format=%B"], cwd=root, capture_output=True, text=True).stdout
except OSError:
    head_msg = ""
head_msg = re.sub(r'"[^"\n]*"|“[^”\n]*”', "", head_msg)  # quoted mentions are not claims
# only the records-commit idiom counts: "remove LOCK" as an item of the message (start, or after ; , : or "and"),
# not a sentence about LOCK removal (the commit introducing this rule said "removes the LOCK" and failed it)
if re.search(r"(?im)(?:^|[;,:]\s*|\band\s+)(?:remove|removed)\s+(?:the\s+)?LOCK\b", head_msg) and (root / "LOCK").exists():
    errors.append("LOCK: the HEAD commit message says it removes the LOCK, but LOCK is still in the tree "
                  "(stage the deletion: git rm LOCK)")

if errors:
    print("GOAL GUARD FAILED:\n" + "\n".join("  " + e for e in errors))
    sys.exit(1)
print("goal guard: ok")
