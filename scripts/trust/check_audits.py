#!/usr/bin/env python3
"""Closed audits stay closed (run 2026-11-04T1028Z, red team G d03): scripts/trust/audits.txt may only
shrink with a LEDGER.md addition naming each removed theorem. Usage: check_audits.py <base commit>.
The Lean side (scripts/trust/AuditClosed.lean, CI work job) checks every listed theorem is sorry-free.

Closed run records stay closed (run 2026-11-07T1828Z, after reading blind red team T d05 — not blind): a file under
`runs/<id>/` that exists at the base may not be modified, renamed or deleted when run <id> started more than
OPEN_HOURS before the newest run folder, unless a LEDGER.md addition names its path. T d05 edited the fidelity
audit of run 2026-10-30T0828Z ("Scope: Lean covers every curvature") a week later; no script read it. A run's
record is evidence of what was checked when; later corrections go into new records."""
import re, subprocess, sys
from datetime import datetime, timedelta
from pathlib import Path
ROOT = Path(__file__).resolve().parents[2]
OPEN_HOURS = 6
RUN = re.compile(r"^runs/(\d{4}-\d\d-\d\dT\d{4}Z)/")


def run_time(rid):
    return datetime.strptime(rid, "%Y-%m-%dT%H%MZ")


def closed_records(base, added, root=None):
    """paths of closed run records changed by a commit since base (closed = the record's run started more than
    OPEN_HOURS before the newest run folder of that commit) and not named by an added LEDGER line"""
    def git(*a):
        r = subprocess.run(["git", *a], cwd=root or ROOT, capture_output=True, text=True)
        return r.stdout if r.returncode == 0 else None
    revs = git("rev-list", "--no-merges", f"{base}..HEAD")
    if revs is None:
        return []
    bad = []
    for c in revs.split():
        ids = [l.rsplit("/", 1)[-1] for l in (git("ls-tree", "--name-only", c, "runs/") or "").split()]
        ids = [i for i in ids if re.fullmatch(r"\d{4}-\d\d-\d\dT\d{4}Z", i)]
        if not ids:
            continue
        newest = max(run_time(i) for i in ids)
        for line in (git("diff-tree", "--no-commit-id", "-r", "-M", "--name-status", f"{c}^", c, "--", "runs/") or "").splitlines():
            parts = line.split("\t")
            if len(parts) < 2 or parts[0].startswith("A"):
                continue
            path = parts[1]  # the pre-existing path (for R, the old name)
            m = RUN.match(path)
            if m and run_time(m.group(1)) < newest - timedelta(hours=OPEN_HOURS) and path not in added:
                bad.append(f"{parts[0][0]} {path} ({c[:7]})")
    return sorted(set(bad))

def control():
    """R1's control (every rule ships with one, run 2026-11-07T1428Z): in a scratch repository, an edit of a record
    of a run 7 h older than the newest run folder must be flagged, the same edit named by the LEDGER must not, and an
    edit of the newest run's own record must not."""
    import tempfile
    with tempfile.TemporaryDirectory() as t:
        def g(*a):
            subprocess.run(["git", "-c", "user.email=c@x", "-c", "user.name=ctl", *a], cwd=t, check=True,
                           capture_output=True)
        g("init", "-q")
        for rid in ("2026-01-01T0000Z", "2026-01-01T0700Z"):
            (Path(t) / "runs" / rid).mkdir(parents=True)
            (Path(t) / "runs" / rid / "README.md").write_text("record\n")
        g("add", "-A"); g("commit", "-qm", "base")
        base = subprocess.run(["git", "rev-parse", "HEAD"], cwd=t, capture_output=True, text=True).stdout.strip()
        for rid in ("2026-01-01T0000Z", "2026-01-01T0700Z"):
            (Path(t) / "runs" / rid / "README.md").write_text("record, edited\n")
        g("add", "-A"); g("commit", "-qm", "edit")
        old = "runs/2026-01-01T0000Z/README.md"
        flagged = closed_records(base, "", root=t)
        ok = [b for b in flagged if old in b] and not [b for b in flagged if "0700Z" in b]
        ok = ok and not closed_records(base, f"+ corrected {old}", root=t)
    if not ok:
        sys.exit("check_audits: R1 failed its control (closed run records rule dead or too broad)")


def names(text):
    return {l.strip() for l in text.splitlines() if l.strip() and not l.startswith("#")}


def main():
    control()
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
    closed = closed_records(base, added)
    print(f"check_audits: {len(closed)} closed run records changed without a LEDGER.md addition naming them")
    errs = []
    if undisclosed:
        errs.append(f"audits.txt lost closed audit theorems without a LEDGER.md addition naming them: {undisclosed}")
    if closed:
        errs.append(f"closed run records (runs/<id>/ older than {OPEN_HOURS} h before the newest run) changed: {closed}")
    if errs:
        sys.exit("; ".join(errs))

main()
