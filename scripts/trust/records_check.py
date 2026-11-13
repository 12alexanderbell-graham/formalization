#!/usr/bin/env python3
"""Run every Lean-free check of CI on the records as they stand now (run 2026-11-13T0428Z, annex LIV).

Why: run 2026-11-13T0228Z ran the local CI replica (`local_frozen_step.py --trust`), then edited STATE.md in its final
records commit; a status line of that edit used two words ('independent', 'only') that check_status_lines S2 rejects,
so the checked job of its final push a3f99fd fails on prose alone (found by run 0428Z with this script's commands).
The full replica costs ≈ 20 min (StatementDeps, Claims); the Python checks cost ≈ 1 min and read only committed files
and the `.lake/*.jsonl` / `*.tsv` of the last StatementDeps run, which stay valid while no `.lean` file changes.
So: run this after the LAST edit of any record (STATE, FINDINGS, LEDGER, README, registries), before the final push.

It runs, in CI's order: goal_guard, make_packet --check, every `python3` command of lean.yml's trust step, then every
`python3` command of the frozen step with BASE set. All commands run; exit 1 if any fails. It does not replace the
Lean steps: after a `.lean` change, rerun StatementDeps (and Claims) first, or use `local_frozen_step.py --trust`.

Usage: python3 scripts/trust/records_check.py <base-sha>   (base = newest ancestor whose whole CI run was green)
"""
import os
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(Path(__file__).resolve().parent))
from local_frozen_step import TRUST_STEP, step_block, step_commands  # noqa: E402


def commands(yml):
    trust = [l.strip() for l in step_block(yml, TRUST_STEP).splitlines() if l.strip().startswith("python3")]
    frozen = [c for c in step_commands(yml) if c.startswith("python3")]
    # precheck_citations (run 2026-11-13T2028Z): the citation registry rule lives in StatementDeps (Lean); run 1828Z
    # changed FINDINGS.md citations with Python checks only and every push from af2cc09 would have failed the trust step
    return (["python3 scripts/goal_guard.py", "python3 validation/make_packet.py --check",
             "python3 scripts/trust/precheck_citations.py"] + trust + frozen)


def main():
    if len(sys.argv) != 2:
        print(__doc__)
        return 2
    base = sys.argv[1]
    if not (ROOT / ".lake/meaning.jsonl").exists():
        print("records_check: .lake/meaning.jsonl missing — run `lake env lean scripts/trust/StatementDeps.lean` first")
        return 2
    env = dict(os.environ, BASE=base)
    failed = []
    cmds = commands((ROOT / ".github/workflows/lean.yml").read_text())
    for c in cmds:
        r = subprocess.run(["bash", "-c", c], cwd=ROOT, env=env, capture_output=True, text=True)
        if r.returncode != 0:
            out = (r.stdout + r.stderr).strip().splitlines()
            failed.append(c)
            print(f"FAIL {c}")
            for l in [l for l in out if "error" in l.lower() or "fail" in l.lower() or l.startswith("  ")][:6]:
                print("    " + l[:300])
    print(f"records_check: {len(cmds)} commands, {len(failed)} failed (base {base})")
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
