#!/usr/bin/env bash
# Restore the CI judge's build of Checked into this checkout (run 2026-11-12T0427Z, annex LIV; see LEDGER).
#
# Why: every scheduled run starts in a fresh container and spent 60–100 min on `lake build Checked`.
# The checked job uploads its build as the artifact `checked-build` (a zstd tarball of .lake/build).
# Lake's traces are content hashes, so restored modules whose sources and imports are unchanged are
# replayed, and only changed modules are rebuilt. A restored build is never evidence: CI judges every push.
#
# Usage (after `lake exe cache get`):
#   1. GitHub MCP: actions_list list_workflow_runs (branch main) → newest run whose checked job got past
#      the build; actions_list list_workflow_run_artifacts <run id> → id of `checked-build`;
#      actions_get download_workflow_run_artifact <artifact id> → a short-lived URL.
#   2. scripts/restore_checked_build.sh '<URL>'      (or a local path to the downloaded .zip)
#   3. lake build Checked    (rebuilds only what changed since the artifact's commit)
#
# Refuses to overwrite an existing .lake/build unless FORCE=1 (a run's own newer build is worth more).
set -euo pipefail
src="${1:?usage: restore_checked_build.sh <artifact URL or zip path>}"
root="$(git rev-parse --show-toplevel)"
cd "$root"
if [ -e .lake/build ] && [ "${FORCE:-0}" != "1" ]; then
  echo "refusing: .lake/build exists (set FORCE=1 to replace it)" >&2
  exit 2
fi
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT
if [ -f "$src" ]; then
  cp "$src" "$tmp/a.zip"
else
  curl -sSfL --retry 5 -o "$tmp/a.zip" "$src"
fi
unzip -q "$tmp/a.zip" -d "$tmp/x"
tarball="$(find "$tmp/x" -name 'checked-build.tar.zst' | head -1)"
[ -n "$tarball" ] || { echo "no checked-build.tar.zst in the artifact" >&2; exit 3; }
# Only .lake/build/... members are accepted (no absolute paths, no ..).
if zstd -dc "$tarball" | tar -tf - | grep -vE '^\.lake/build(/|$)' | grep -q .; then
  echo "artifact contains paths outside .lake/build; refusing" >&2
  exit 4
fi
if zstd -dc "$tarball" | tar -tf - | grep -q '\.\./'; then
  echo "artifact contains '..' paths; refusing" >&2
  exit 4
fi
rm -rf .lake/build
mkdir -p .lake
zstd -dc "$tarball" | tar -xf - --no-same-owner
echo "restored .lake/build from commit $(cat .lake/build/CHECKED_BUILD_COMMIT 2>/dev/null || echo '?')"
echo "next: lake build Checked   (rebuilds only modules changed since that commit)"
