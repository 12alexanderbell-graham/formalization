#!/usr/bin/env bash
# Start-of-run setup for a scheduled run (run 2026-11-21T0028Z, annex LIV; see LEDGER).
#
# Why: eleven runs in a row (2026-11-20T0028Z ... 2026-11-21T0028Z) found the session's clone on a stale
# divergent `main` (tip fa47717, whose commits are on origin/wip/leanchecker-shards), reset it by hand with
# slightly different commands, and then installed elan and the Mathlib cache step by step. This script does
# the mechanical part the same way every time and prints what is left (the judge's build needs a short-lived
# artifact URL that only the GitHub MCP tools can produce).
#
# Usage:  scripts/start_run.sh            (from anywhere inside the clone)
# Safe:   it never pushes and never discards commits that exist only locally: if local main has commits
#         that no remote branch contains, it stops and lists them.
set -euo pipefail
root="$(git rev-parse --show-toplevel)"
cd "$root"

echo "== git"
git fetch --quiet origin
if [ -f .git/shallow ]; then git fetch --quiet --unshallow origin || true; fi
cur="$(git rev-parse --abbrev-ref HEAD)"
if [ "$cur" != "main" ]; then git checkout --quiet main 2>/dev/null || git checkout --quiet -B main origin/main; fi
only_local="$(git rev-list main --not --remotes=origin | head -5)"
if [ -n "$only_local" ]; then
  echo "STOP: local main has commits on no origin branch (not reset):"
  git log --oneline main --not --remotes=origin | head -10
  exit 3
fi
if [ "$(git rev-parse main)" != "$(git rev-parse origin/main)" ]; then
  echo "local main $(git rev-parse --short main) -> origin/main $(git rev-parse --short origin/main) (every local commit is on an origin branch)"
  git checkout --quiet -B main origin/main
fi
git log --oneline -1 | cut -c1-120

echo "== LOCK (48.4)"
if [ -f LOCK ]; then cat LOCK; else echo "no LOCK"; fi

echo "== Lean"
if ! command -v lake >/dev/null 2>&1 && [ ! -x "$HOME/.elan/bin/lake" ]; then
  tmp="$(mktemp -d)"
  curl -sSfL --retry 5 https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -o "$tmp/elan-init.sh"
  sh "$tmp/elan-init.sh" -y --default-toolchain none >/dev/null
  rm -rf "$tmp"
fi
# shellcheck disable=SC1091
source "$HOME/.elan/env"
lean --version
if [ ! -d .lake/packages/mathlib/.lake/build ]; then
  lake exe cache get 2>&1 | tail -2
fi
pip install -q --break-system-packages markdown-it-py==4.2.0 cmarkgfm==2024.11.20 mpmath sympy >/dev/null 2>&1 || true

echo "== next (by hand)"
if [ -e .lake/build ]; then
  echo ".lake/build exists: lake build Checked (in the background; the tool call limit is two minutes)"
else
  echo "1. GitHub MCP: actions_list list_workflow_runs (branch main) -> newest run whose checked job uploaded 'checked-build';"
  echo "   actions_list list_workflow_run_artifacts <id>; actions_get download_workflow_run_artifact <artifact id>"
  echo "2. nohup scripts/restore_checked_build.sh '<URL>' > <scratchpad>/restore.log 2>&1 &   (about one minute; the URL expires ten minutes after it is made)"
  echo "3. nohup lake build Checked > <scratchpad>/build.log 2>&1 &   (replays the restored build, minutes)"
fi
