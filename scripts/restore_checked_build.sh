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
#   2. scripts/restore_checked_build.sh '<URL>'      (streamed; or a local path to the downloaded .zip)
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
# Run 2026-11-20T1628Z (annex LIV): with a URL and STREAM=1 (the default for URLs) the zip never touches the disk.
# The first restore of that run filled the container's allowance (the 2.8 GB zip plus the 17 GB build, beside the
# Mathlib packages) and left truncated .olean files that lake then failed to read. The artifact zip holds one
# stored member `checked-build.tar.zst` (method 0, data-descriptor flag), so its bytes start right after the local
# header: read the header with a range request, stream from that offset into zstd and tar, extract only
# .lake/build/... members (GNU tar skips members with `..`), and refuse the result if it holds a symlink or an
# empty .olean. STREAM=0 keeps the old download-then-unzip route.
if [ ! -f "$src" ] && [ "${STREAM:-1}" = "1" ]; then
  if ! python3 -c 'import zstandard' 2>/dev/null; then
    pip install -q --break-system-packages zstandard >&2 || { echo "no zstandard module" >&2; exit 5; }
  fi
  off="$(curl -sSfL --retry 5 -r 0-29 "$src" | python3 -c '
import sys, struct
b = sys.stdin.buffer.read()
assert b[:4] == b"PK\x03\x04", "not a zip local header"
_, flag, method = struct.unpack("<HHH", b[4:10])
n, e = struct.unpack("<HH", b[26:30])
assert method == 0, "member is compressed (method %d): use STREAM=0" % method
print(30 + n + e)')" || { echo "cannot read the zip header; use STREAM=0" >&2; exit 4; }
  rm -rf .lake/build
  mkdir -p .lake
  set +o pipefail
  curl -sSfL --retry 5 -r "$off"- "$src" | python3 -c '
import sys, zstandard
d = zstandard.ZstdDecompressor().stream_reader(sys.stdin.buffer, read_across_frames=False)
o = sys.stdout.buffer
try:
    while True:
        c = d.read(1 << 20)
        if not c:
            break
        o.write(c)
except zstandard.ZstdError:
    pass  # the zip trailer after the frame; tar below decides whether the archive was complete
' | tar -xf - --no-same-owner --wildcards '.lake/build/*' && rc=0 || rc=$?
  set -o pipefail
  [ "$rc" = "0" ] || { echo "tar failed ($rc); .lake/build is incomplete, remove it" >&2; exit 4; }
  if find .lake/build -type l | grep -q . || find .lake/build -name '*.olean' -size 0 | grep -q .; then
    echo "restored build holds a symlink or an empty .olean; refusing (remove .lake/build)" >&2; exit 4
  fi
  echo "restored .lake/build (streamed) from commit $(cat .lake/build/CHECKED_BUILD_COMMIT 2>/dev/null || echo '?')"
  echo "next: lake build --no-build Checked (lists what is missing), then lake build Checked"
  exit 0
fi
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
# Run 2026-11-15T0628Z: a local zip left in place after the restore took the disk allowance to 1.6 GB (runs 2028Z
# and 2228Z of 2026-11-14 hit the same limit). DELETE_ZIP=1 removes a local zip once the restore has succeeded;
# otherwise say so loudly. (A URL argument downloads into a temporary directory that is removed on exit.)
if [ -f "$src" ]; then
  if [ "${DELETE_ZIP:-0}" = "1" ]; then rm -f -- "$src"; echo "deleted the local zip $src"
  else echo "reminder: delete the local zip $src now (about 2.5 GB), or pass DELETE_ZIP=1 next time" >&2
  fi
fi
echo "next: lake build Checked   (rebuilds only modules changed since that commit)"
