#!/usr/bin/env python3
"""CI helper (part of the judge, annex 39.5; run 2026-11-07T0428Z, see LEDGER).

Why: CI was saturated (every push started a checked job of hours, 20+ runs queued). The workflow now
coalesces queued work per ref (concurrency groups, cancel-in-progress false: a running job always
finishes, a newer push replaces an older *queued* one; per heavy job since run 2026-11-07T0628Z). The base-diff checks (check_relock, check_audits,
check_blind_route, ...) used `github.event.before`, so a coalesced commit's diff would have gone
unchecked. They now diff against BASE = the newest ancestor of HEAD whose whole workflow run concluded
`success` (from the Actions API; durable run records, not caches). Every change since the last fully
green commit is therefore checked, however many runs were coalesced in between. The checks were
verified to work over multi-commit ranges (run 2026-11-07T0428Z README).

Prints GitHub step outputs:

  base=<sha>            newest green ancestor (may be HEAD itself on a re-run)
  base_run=<run id>     the run that made it green
  lock_only=true|false  true only if BASE is a proper ancestor of HEAD and every file changed between
                        them is LOCK (a heartbeat on top of a judged tree). Then the Lean jobs are
                        skipped (shown as skipped). Anything else runs every job.
  checked_hash=<sha256> SHA-256 over the paths and contents of every tracked file that decides what
                        nanoda checks (Checked/**, Checked.lean, lakefile.toml, lake-manifest.json,
                        lean-toolchain, scripts/nanoda_checked.sh, scripts/nanoda_shard.sh, scripts/nanoda/, the workflow file). The nanoda job
                        memoises a pass under this hash.

Fail-closed: if the API cannot be read after 5 attempts (transient 5xx/429/timeouts retried) or no green ancestor is found among the last 3000 commits,
the script exits non-zero, the changes job fails and every dependent job is skipped (run red).

Usage in CI: python3 scripts/ci_changes.py >> "$GITHUB_OUTPUT"   (env GITHUB_REPOSITORY, GH_TOKEN)
Local:       python3 scripts/ci_changes.py --base <sha>          (skips the API)
Self-test:   python3 scripts/ci_changes.py --selftest
"""
import hashlib
import json
import os
import subprocess
import sys
import urllib.request

HASHED = ["Checked", "Checked.lean", "lakefile.toml", "lake-manifest.json", "lean-toolchain",
          "scripts/nanoda_checked.sh", "scripts/nanoda_shard.sh", "scripts/nanoda", ".github/workflows/lean.yml"]
WORKFLOW = "lean.yml"
PAGES = 10          # 10 x 100 most recent successful runs
MAX_ANCESTORS = 3000


def git(*args, check=True):
    r = subprocess.run(["git", *args], capture_output=True, text=True)
    if check and r.returncode != 0:
        raise RuntimeError(f"git {' '.join(args)}: {r.stderr.strip()}")
    return r


def fetch_json(req, attempts=5, wait=15):
    """GET with retries on transient failures (HTTP 5xx, 429, timeouts, connection errors).

    Run 2026-11-08T0228Z: heartbeat dce69bf went red on a single HTTP 504 from the Actions API.
    Retrying does not weaken the gate: after the last attempt the error propagates (fail-closed),
    and a 4xx other than 429 is never retried."""
    import time
    import urllib.error
    for i in range(attempts):
        try:
            with urllib.request.urlopen(req, timeout=60) as r:
                return json.load(r)
        except urllib.error.HTTPError as e:
            if not (e.code >= 500 or e.code == 429) or i == attempts - 1:
                raise
        except (urllib.error.URLError, TimeoutError, ConnectionError):
            if i == attempts - 1:
                raise
        time.sleep(wait * (i + 1))
    raise RuntimeError("unreachable")


def green_runs():
    """head_sha -> run id of successful runs of this workflow (newest first)."""
    repo = os.environ["GITHUB_REPOSITORY"]
    token = os.environ["GH_TOKEN"]
    out = {}
    for page in range(1, PAGES + 1):
        url = (f"https://api.github.com/repos/{repo}/actions/workflows/{WORKFLOW}/runs"
               f"?status=success&per_page=100&page={page}")
        req = urllib.request.Request(url, headers={"Authorization": f"Bearer {token}",
                                                   "Accept": "application/vnd.github+json"})
        runs = fetch_json(req).get("workflow_runs", [])
        for run in runs:
            if run.get("conclusion") == "success":
                out.setdefault(run["head_sha"], run["id"])
        if len(runs) < 100:
            break
    return out


def newest_green_ancestor(green):
    for sha in git("rev-list", f"--max-count={MAX_ANCESTORS}", "HEAD").stdout.split():
        if sha in green:
            return sha, green[sha]
    return None, None


def lock_only(base: str) -> bool:
    head = git("rev-parse", "HEAD").stdout.strip()
    if not base or git("rev-parse", base).stdout.strip() == head:
        return False
    if git("merge-base", "--is-ancestor", base, "HEAD", check=False).returncode != 0:
        return False
    changed = [p for p in git("diff", "--name-only", "--no-renames", base, "HEAD").stdout.splitlines() if p]
    return bool(changed) and all(p == "LOCK" for p in changed)


def checked_hash() -> str:
    files = sorted(set(git("ls-files", "-z", "--", *HASHED).stdout.split("\0")) - {""})
    h = hashlib.sha256()
    for f in files:
        h.update(f.encode() + b"\0")
        h.update(subprocess.run(["git", "show", f"HEAD:{f}"], capture_output=True, check=True).stdout)
        h.update(b"\0")
    return h.hexdigest()


def selftest():
    import tempfile
    cwd = os.getcwd()
    with tempfile.TemporaryDirectory() as d:
        os.chdir(d)
        try:
            for c in (["init", "-q"], ["config", "user.email", "t@t"], ["config", "user.name", "t"]):
                git(*c)

            def commit(path, text):
                with open(path, "w") as fh:
                    fh.write(text)
                git("add", path)
                git("commit", "-qm", path)
                return git("rev-parse", "HEAD").stdout.strip()
            a = commit("Checked.lean", "x")
            b = commit("LOCK", "held")
            assert lock_only(a), "LOCK-only diff from a green ancestor must be lock_only"
            assert not lock_only(b), "BASE == HEAD must run"
            assert not lock_only(""), "no base must run"
            h1 = checked_hash()
            c = commit("STATE.md", "y")
            d2 = commit("LOCK", "beat")
            assert not lock_only(a), "LOCK plus another file since the green base must run"
            assert lock_only(c), "heartbeat on a judged tree is lock_only"
            # coalescing: green = {a}; c (records) was never judged; the heartbeat d2 must run fully
            assert newest_green_ancestor({a: 1}) == (a, 1)
            assert not lock_only(newest_green_ancestor({a: 1})[0]), "unjudged commit below a heartbeat must run"
            assert newest_green_ancestor({a: 1, c: 2}) == (c, 2)
            assert newest_green_ancestor({}) == (None, None)
            assert checked_hash() == h1, "records and LOCK do not change the nanoda input"
            commit("Checked.lean", "z")
            assert checked_hash() != h1, "a Checked change must change the hash"
            git("checkout", "-q", "-b", "side", a)
            commit("LOCK", "other")
            assert not lock_only(d2), "non-ancestor base must run"
            assert newest_green_ancestor({c: 2, d2: 3}) == (None, None), "only ancestors count"
        finally:
            os.chdir(cwd)
    print("ci_changes selftest: ok")


def main(argv):
    if argv == ["--selftest"]:
        selftest()
        return 0
    if len(argv) == 2 and argv[0] == "--base":
        base, run = git("rev-parse", argv[1]).stdout.strip(), "local"
    else:
        try:
            green = green_runs()
        except Exception as e:  # fail-closed
            print(f"::error::ci_changes: cannot read successful runs from the Actions API: {e}", file=sys.stderr)
            return 1
        base, run = newest_green_ancestor(green)
        if base is None:
            print(f"::error::ci_changes: no ancestor of HEAD among {len(green)} green runs", file=sys.stderr)
            return 1
    print(f"base={base}")
    print(f"base_run={run}")
    print(f"lock_only={'true' if lock_only(base) else 'false'}")
    print(f"checked_hash={checked_hash()}")
    print(f"ci_changes: base {base} (run {run}), HEAD {git('rev-parse', 'HEAD').stdout.strip()}", file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
