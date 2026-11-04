#!/usr/bin/env python3
"""Closed audits stay closed (run 2026-11-04T1028Z, red team G d03): scripts/trust/audits.txt may only
shrink with a LEDGER.md addition naming each removed theorem. Usage: check_audits.py <base commit>.
The Lean side (scripts/trust/AuditClosed.lean, CI work job) checks every listed theorem is sorry-free."""
import subprocess, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[2]

def names(text):
    return {l.strip() for l in text.splitlines() if l.strip() and not l.startswith("#")}

def main():
    base = sys.argv[1] if len(sys.argv) > 1 else ""
    now = names((ROOT / "scripts/trust/audits.txt").read_text())
    r = subprocess.run(["git", "show", f"{base}:scripts/trust/audits.txt"], cwd=ROOT, capture_output=True, text=True)
    if not base or r.returncode:
        print(f"check_audits: {len(now)} closed audit theorems (no base list to compare)")
        return
    lost = names(r.stdout) - now
    d = subprocess.run(["git", "diff", base, "HEAD", "--", "LEDGER.md"], cwd=ROOT, capture_output=True, text=True)
    added = "\n".join(l for l in d.stdout.splitlines() if l.startswith("+"))
    undisclosed = sorted(n for n in lost if n.split(".")[-1] not in added)
    print(f"check_audits: {len(now)} closed audit theorems; {len(lost)} removed since {base}")
    if undisclosed:
        sys.exit(f"audits.txt lost closed audit theorems without a LEDGER.md addition naming them: {undisclosed}")

main()
