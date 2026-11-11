#!/usr/bin/env python3
"""Run the checked job's base-diff step locally, exactly as CI runs it (run 2026-11-11T1428Z).

Why: run 2026-11-11T1028Z merged two promotions after running "every trust-step Python check" locally, but
not the `--base` checks of the step "Frozen statements and definitions change only with a LEDGER entry ..."
(lean.yml). CI then failed there (run 43031110000, check_necessity N2: a new headline disclosed in LEDGER by
its short name, while N2 matches the name exactly as TRUST_MAP.md prints it). Hand-copied command lists drift;
this script reads the step's `run:` block from `.github/workflows/lean.yml` itself and runs every command in it
with `$BASE` set, after `lake env lean scripts/trust/StatementDeps.lean` has written `.lake/meaning.jsonl`.

Usage: python3 scripts/trust/local_frozen_step.py [--trust] <base-sha>   (exit 1 if any command fails; all are run)
`--trust` first runs the preceding step ("Statement dependencies, trust map, ...": StatementDeps, Claims and
the Python trust suite, including the staleness checks of TRUST_MAP.md, CLAIMS.md, PHRASE_LINES.md) as one
`bash -e` script, as CI does; commit regenerated files before relying on its staleness checks.
The base is the newest ancestor whose whole CI run was green (`scripts/ci_changes.py` computes it in CI).
"""
import os
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
STEP = "- name: Frozen statements and definitions change only with a LEDGER entry naming them"


TRUST_STEP = "- name: Statement dependencies, trust map, non-vacuity witnesses"


def step_block(yml, name):
    lines = yml.splitlines()
    start = next(i for i, l in enumerate(lines) if l.strip().startswith(name))
    run = next(i for i in range(start, len(lines)) if lines[i].strip() == "run: |")
    ind = len(lines[run + 1]) - len(lines[run + 1].lstrip())
    out = []
    for l in lines[run + 1:]:
        if l.strip() and len(l) - len(l.lstrip()) < ind:
            break
        out.append(l[ind:])
    return "\n".join(out) + "\n"


def step_commands(yml):
    lines = yml.splitlines()
    start = next(i for i, l in enumerate(lines) if l.strip().startswith(STEP))
    run = next(i for i in range(start, len(lines)) if lines[i].strip() == "run: |")
    ind = len(lines[run + 1]) - len(lines[run + 1].lstrip())
    cmds = []
    for l in lines[run + 1:]:
        if l.strip() and len(l) - len(l.lstrip()) < ind:
            break
        s = l.strip()
        if s and not s.startswith("#"):
            cmds.append(s)
    return cmds


def main():
    args = [a for a in sys.argv[1:] if a != "--trust"]
    if len(args) != 1:
        print(__doc__)
        return 2
    sys.argv[1:] = args
    yml = (ROOT / ".github/workflows/lean.yml").read_text()
    if TRUST:
        r = subprocess.run(["bash", "-e", "-c", step_block(yml, TRUST_STEP)], cwd=ROOT)
        print(f"local trust step: exit {r.returncode}")
        if r.returncode != 0:
            return 1
    if not (ROOT / ".lake/meaning.jsonl").exists():
        print("run `lake env lean scripts/trust/StatementDeps.lean` first (.lake/meaning.jsonl missing)")
        return 2
    env = dict(os.environ, BASE=sys.argv[1])
    cmds = step_commands(yml)
    bad = 0
    for c in cmds:
        r = subprocess.run(c, shell=True, cwd=ROOT, env=env, capture_output=True, text=True)
        if r.returncode != 0:
            bad += 1
            print(f"FAIL: {c}\n{(r.stdout + r.stderr)[-3000:]}")
    print(f"local frozen step: {len(cmds)} commands, {bad} failed (base {sys.argv[1]})")
    return 1 if bad else 0


TRUST = "--trust" in sys.argv[1:]

if __name__ == "__main__":
    sys.exit(main())
