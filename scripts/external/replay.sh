#!/usr/bin/env bash
# External replay of one outside Lean result (standing instruction 11; run 2026-11-26T1529Z).
# General: works on any Lake project whose solution closure needs only Mathlib (and Lean core).
#
# Why: outside libraries are often far too large to build whole (OpenAI's math release: 34 top-level
# areas, ~25M lines, 40+ git dependencies, its own README warns against building it at once). A
# result needs only the import closure of its headline module. This script extracts that closure into
# a minimal Lake project pinned to the outside project's own toolchain and Mathlib revision (Mathlib
# from the prebuilt cache), builds it, and runs the program's judges on it:
#   1. Match: the frozen challenge file, verbatim in namespace `Chal`, with its `sorry` replaced by
#      the solution theorem; it compiles only if the solution proves the challenge statement with the
#      challenge's definitions (definitional unfolding allowed). Same question as leanprover/comparator,
#      without its sandbox (landrun) and export dependencies.
#   2. `#print axioms` of the matched theorem: only propext, Classical.choice, Quot.sound accepted.
#   3. leanchecker: the toolchain kernel replays every declaration of every copied module.
#   4. nanoda (independent type checker, Rust): checks the export of the matched theorem and all its
#      dependencies (Mathlib included) when NANODA=1 and the tools are present.
#   5. scan_escapes.py over the closure (advisory).
#
# Usage:
#   scripts/external/replay.sh <outside lean root> <work dir> <solution module> <challenge module> <theorem> [<theorem>...]
# Environment: NANODA=1 to run step 4 (needs cargo); L4E_DIR / NANODA_DIR to reuse built tools.
#   EXTRA="Lib.Mod=path/to/file.lean ..." adds the program's own files (blind readings, closures,
#   definition pins) as modules of the replay project; they are built, their `#print axioms` lines
#   checked and their libraries replayed by leanchecker too. A closure imports the challenge module and
#   the reading by these module names.
# Exit status non-zero on any failed judge. A closure that needs packages other than Mathlib stops at
# step 0 with the list of packages: that is a blocker to record, not a pass.
set -euo pipefail
OLDPWD_SRC=$(pwd); SRC=$(cd "$1" && pwd); WORK=$2; SOL=$3; CHAL=$4; shift 4; THMS=("$@")
HERE=$(cd "$(dirname "$0")" && pwd)
export PATH="$HOME/.elan/bin:$PATH"
mkdir -p "$WORK"; WORK=$(cd "$WORK" && pwd)
TOOLCHAIN=$(cat "$SRC/lean-toolchain")
MATHLIB_REV=$(python3 -c "import json,sys; m=json.load(open(sys.argv[1])); print([p['rev'] for p in m['packages'] if p['name']=='mathlib'][0])" "$SRC/lake-manifest.json")
echo "== external replay: $SOL / $CHAL; toolchain $TOOLCHAIN; mathlib $MATHLIB_REV"

# 0. closure and its outside packages
python3 - "$SRC" "$WORK" "$SOL" "$CHAL" <<'PY'
import os, re, shutil, sys
src, dst, *mods = sys.argv[1:]
seen, ext = set(), set()
def go(m):
    if m in seen: return
    p = os.path.join(src, m.replace('.', '/') + '.lean')
    if not os.path.exists(p):
        ext.add(m.split('.')[0]); return
    seen.add(m)
    for line in open(p, encoding='utf-8'):
        mm = re.match(r'\s*(?:public\s+)?(?:meta\s+)?import\s+(.*)', line)
        if mm:
            for x in mm.group(1).split(): go(x)
for m in mods: go(m)
bad = sorted(ext - {'Mathlib', 'Lean', 'Init', 'Std'})
if bad:
    print('BLOCKER: closure needs packages other than Mathlib:', bad); sys.exit(3)
for m in seen:
    rel = m.replace('.', '/') + '.lean'
    os.makedirs(os.path.dirname(os.path.join(dst, rel)), exist_ok=True)
    shutil.copy(os.path.join(src, rel), os.path.join(dst, rel))
libs = sorted({m.split('.')[0] for m in seen})
open(os.path.join(dst, 'closure_modules.txt'), 'w').write('\n'.join(sorted(seen)) + '\n')
open(os.path.join(dst, 'closure_libs.txt'), 'w').write(' '.join(libs) + '\n')
print(f'closure: {len(seen)} modules, libraries {libs}')
PY
cd "$WORK"
echo "$TOOLCHAIN" > lean-toolchain
{
  echo 'name = "externalreplay"'
  echo 'defaultTargets = []'
  echo '[leanOptions]'
  echo 'autoImplicit = false'
  echo '[[require]]'
  echo 'name = "mathlib"'
  echo 'git = "https://github.com/leanprover-community/mathlib4.git"'
  echo "rev = \"$MATHLIB_REV\""
  for l in $(cat closure_libs.txt) Match $(for e in ${EXTRA:-}; do echo "${e%%=*}" | cut -d. -f1; done | sort -u); do
    echo '[[lean_lib]]'; echo "name = \"$l\""; done
} > lakefile.toml
[ -d .lake/packages/mathlib ] || lake update > lake_update.log 2>&1
lake exe cache get > cache.log 2>&1 || true

# 1. Match file
mkdir -p Match
CH_FILE=${CHAL//.//}.lean
MATCH_MOD=Match.$(basename "${CHAL//.//}")
python3 - "$CH_FILE" "$SOL" "$MATCH_MOD" "${THMS[@]}" <<'PY'
import re, sys
ch, sol, matchmod, *thms = sys.argv[1:]
src = open(ch, encoding='utf-8').read()
body = re.sub(r'^\s*import\s+.*\n', '', src, flags=re.M)
top = sorted({t.split('.')[0] for t in thms})
for t in top:
    body = re.sub(r'^namespace ' + t + r'\b', 'namespace Chal', body, flags=re.M)
    body = re.sub(r'^end ' + t + r'\b', 'end Chal', body, flags=re.M)
for t in thms:
    name = t.split('.')[-1]
    body, n = re.subn(r'(theorem\s+' + re.escape(name) + r'\b[\s\S]*?:=)\s*by\s*\n?\s*sorry',
                      r'\1 by exact ' + t, body, count=1)
    if n != 1: sys.exit(f'could not find `theorem {name} ... := by sorry` in {ch}')
code_only = re.sub(r'--[^\n]*', '', re.sub(r'/-.*?-/', '', body, flags=re.S))
if re.search(r'\bsorry\b', code_only): sys.exit('challenge has a sorry the script did not replace')
chal_names = ['Chal.' + t.split('.', 1)[1] for t in thms]
out = f'import {sol}\n' + body + '\n' + ''.join(f'#print axioms {c}\n' for c in chal_names)
open(matchmod.replace('.', '/') + '.lean', 'w', encoding='utf-8').write(out)
open('match_names.txt', 'w').write(' '.join(chal_names) + '\n')
PY
lake build "$SOL" "$CHAL" > build.log 2>&1 || { tail -40 build.log; echo "FAIL: build"; exit 1; }
lake env lean "${MATCH_MOD//.//}.lean" > match.log 2>&1 || { cat match.log; echo "FAIL: match"; exit 1; }
cat match.log
if grep -q "error" match.log; then echo "FAIL: match has errors"; exit 1; fi
# 2. axioms
if grep "depends on axioms" match.log | grep -v "depends on axioms: \[propext, Classical.choice, Quot.sound\]" | grep -q .; then
  echo "FAIL: axioms beyond propext, Classical.choice, Quot.sound"; exit 1; fi
lake build "$MATCH_MOD" > build_match.log 2>&1 || { tail -20 build_match.log; echo "FAIL: build match module"; exit 1; }
# 2b. the program's own files (readings, closures, pins)
EXTRA_LIBS=""
for e in ${EXTRA:-}; do
  mod=${e%%=*}; file=${e#*=}; rel=${mod//.//}.lean
  mkdir -p "$(dirname "$rel")"; cp "$OLDPWD_SRC/$file" "$rel" 2>/dev/null || cp "$file" "$rel"
  EXTRA_LIBS="$EXTRA_LIBS $(echo "$mod" | cut -d. -f1)"
done
for e in ${EXTRA:-}; do
  mod=${e%%=*}
  lake build "$mod" > "build_$mod.log" 2>&1 || { tail -30 "build_$mod.log"; echo "FAIL: build $mod"; exit 1; }
  lake env lean "${mod//.//}.lean" > "check_$mod.log" 2>&1 || true
  if grep -q "error" "check_$mod.log"; then cat "check_$mod.log"; echo "FAIL: $mod has errors"; exit 1; fi
  if grep "depends on axioms" "check_$mod.log" | grep -v "depends on axioms: \[propext, Classical.choice, Quot.sound\]" | grep -q .; then
    grep "depends on axioms" "check_$mod.log"; echo "FAIL: $mod axioms"; exit 1; fi
  grep "depends on axioms" "check_$mod.log" || true
done
EXTRA_LIBS=$(echo "$EXTRA_LIBS" | tr ' ' '\n' | sort -u | tr '\n' ' ')
# 3. leanchecker on every copied module and the match module
# One module per leanchecker process: a single process over a large closure was killed by the memory
# limit of the session sandbox (run 2026-11-26T1529Z: 4.5 GB anonymous memory on 58 modules).
: > leanchecker.log
for m in $(cat closure_modules.txt) "$MATCH_MOD" ${EXTRA:+$(for e in $EXTRA; do echo "${e%%=*}"; done)}; do
  lake env leanchecker "$m" >> leanchecker.log 2>&1 || { tail -20 leanchecker.log; echo "FAIL: leanchecker $m"; exit 1; }
done
echo "leanchecker: replayed $(wc -l < closure_modules.txt) closure modules, the match module and ${EXTRA:+the extra modules}: OK"
# 4. nanoda (optional)
if [ "${NANODA:-0}" = 1 ]; then
  L4E=${L4E_DIR:-$WORK/_lean4export}; NAN=${NANODA_DIR:-$WORK/_nanoda_lib}
  if [ ! -x "$L4E/.lake/build/bin/lean4export" ]; then
    git clone -q https://github.com/leanprover/lean4export.git "$L4E"
    tag=$(echo "$TOOLCHAIN" | sed -E 's/.*:(v[0-9]+\.[0-9]+)\..*/\1.0/')
    (cd "$L4E" && git checkout -q "$tag" && echo "$TOOLCHAIN" > lean-toolchain && lake build > /dev/null)
  fi
  if [ ! -x "$NAN/target/release/nanoda_bin" ]; then
    git clone -q https://github.com/ammkrn/nanoda_lib.git "$NAN"
    (cd "$NAN" && git checkout -q 8de7e0c4ed3052745a7f8725164efd9e76d84c56 && cargo build --release -q)
  fi
  # shellcheck disable=SC2046
  lake env "$L4E/.lake/build/bin/lean4export" "$MATCH_MOD" -- $(cat match_names.txt) > export.ndjson
  cat > nanoda.json <<CFG
{ "export_file_path": "export.ndjson", "use_stdin": false,
  "permitted_axioms": ["propext", "Classical.choice", "Quot.sound"],
  "unpermitted_axiom_hard_error": true, "nat_extension": true, "string_extension": true,
  "print_success_message": true }
CFG
  "$NAN/target/release/nanoda_bin" nanoda.json > nanoda.log 2>&1 || { tail -20 nanoda.log; echo "FAIL: nanoda"; exit 1; }
  tail -3 nanoda.log; echo "nanoda: OK ($(wc -l < export.ndjson) export lines)"
fi
# 5. advisory scan
python3 "$HERE/scan_escapes.py" "$WORK" "$SOL" | tail -2
echo "== external replay PASSED: $SOL proves $CHAL (${THMS[*]})"
