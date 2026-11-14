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
# Disk (run 2026-11-14T0828Z): the build unpacks to ≈ 15 GB. The zip is never copied and the tarball is
# streamed out of it (no unzipped copy), so the peak is the zip plus the build; a local zip is read in place.
if [ -f "$src" ]; then
  zip="$src"
else
  zip="$tmp/a.zip"
  curl -sSfL --retry 5 -o "$zip" "$src"
fi
member="$(unzip -Z1 "$zip" | grep -E '(^|/)checked-build\.tar\.zst$' | head -1)"
[ -n "$member" ] || { echo "no checked-build.tar.zst in the artifact" >&2; exit 3; }
avail_kb="$(df -Pk . | awk 'NR==2 {print $4}')"
if [ "${avail_kb:-0}" -lt 16000000 ]; then
  echo "warning: only $((avail_kb / 1000000)) GB free; the restored build needs about 15 GB (delete ~/.cache/mathlib and old zips first)" >&2
fi
# Decompressor (stdin to stdout): the zstd binary, else Python's `zstandard` (pip install --break-system-packages zstandard).
unz() {
  if command -v zstd >/dev/null 2>&1; then zstd -dc
  else python3 -c 'import sys, zstandard; zstandard.ZstdDecompressor().copy_stream(sys.stdin.buffer, sys.stdout.buffer)'
  fi
}
# Run 2026-11-14T1228Z: a fresh container has neither; the listing then failed only after the 2.5 GB download.
# Install the Python module up front (robustness only; no check changes).
if ! command -v zstd >/dev/null 2>&1 && ! python3 -c 'import zstandard' 2>/dev/null; then
  pip install -q --break-system-packages zstandard >&2 || { echo "no zstd decompressor (install zstd or zstandard)" >&2; exit 5; }
fi
# Only .lake/build/... members are accepted (no absolute paths, no ..); a failed listing refuses.
unzip -p "$zip" "$member" | unz | tar -tf - > "$tmp/members" || { echo "cannot list the artifact; refusing" >&2; exit 4; }
[ -s "$tmp/members" ] || { echo "empty artifact; refusing" >&2; exit 4; }
if grep -vE '^\.lake/build(/|$)' "$tmp/members" | grep -q . || grep -q '\.\./' "$tmp/members"; then
  echo "artifact contains paths outside .lake/build; refusing" >&2
  exit 4
fi
rm -rf .lake/build
mkdir -p .lake
unzip -p "$zip" "$member" | unz | tar -xf - --no-same-owner
echo "restored .lake/build from commit $(cat .lake/build/CHECKED_BUILD_COMMIT 2>/dev/null || echo '?')"
echo "next: lake build Checked   (rebuilds only modules changed since that commit)"
