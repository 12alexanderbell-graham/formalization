#!/usr/bin/env bash
# External replay of one outside Lean result (standing instruction 11; run 2026-11-26T1529Z).
# General: works on any Lake project whose solution closure needs only Mathlib (and Lean core).
#
# Why: outside libraries are often far too large to build whole (OpenAI's math release: 34 top-level
# areas, ~25M lines, 40+ git dependencies, its own README warns against building it at once). A
# result needs only the import closure of its headline module. This script extracts that closure into
# a minimal Lake project pinned to the outside project's own toolchain and Mathlib revision (Mathlib
# from the prebuilt cache), builds it, and runs the program's judges on it:
#   1. Compare (scripts/external/compare_decls.lean): every declaration of the challenge module must exist
#      in the solution environment with the same kind, universes, type and (for definitions) value;
#      the target theorems' statements are thereby identical; read from the challenge .olean, so only
#      one environment is loaded. Same question as leanprover/comparator, without its sandbox.
#      (Until run 2026-11-26T1529Z this step copied the challenge into `namespace Chal` and proved it by
#      the solution theorem: unsound for `structure`s, which become new types — T1 replay failure,
#      diagnosed in a chat session.)
#   2. Axioms of each target theorem in the solution environment: only propext, Classical.choice,
#      Quot.sound accepted (checked by compare_decls).
#   3. leanchecker: the toolchain kernel replays every declaration of every copied module.
#   4. nanoda (independent type checker, Rust): checks the export of the target theorems and all their
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
seen, ext, where = set(), set(), {}
# Modules resolve under the project root and under its lakefile's top-level `srcDir` (target R's
# editions keep their library in src/ and Challenge.lean at the root; run 2026-11-27T0628Z).
roots = [src]
lt = os.path.join(src, 'lakefile.toml')
if os.path.exists(lt):
    head = re.split(r'^\[', open(lt, encoding='utf-8').read(), maxsplit=1, flags=re.M)[0]
    sd = re.search(r'^srcDir\s*=\s*"([^"]+)"', head, flags=re.M)
    if sd: roots.append(os.path.join(src, sd.group(1)))
def go(m):
    if m in seen: return
    cands = [os.path.join(r, m.replace('.', '/') + '.lean') for r in roots]
    cands = [c for c in cands if os.path.exists(c)]
    if not cands:
        ext.add(m.split('.')[0]); return
    p = where[m] = cands[0]
    seen.add(m)
    for line in open(p, encoding='utf-8'):
        mm = re.match(r'\s*(?:public\s+)?(?:meta\s+)?import\s+(.*)', line)
        if mm:
            for x in mm.group(1).split(): go(x)
for m in mods: go(m)
bad = sorted(ext - {'Mathlib', 'Lean', 'Init', 'Std', 'Lake', 'Batteries', 'Aesop', 'Qq', 'Plausible', 'ProofWidgets', 'LeanSearchClient', 'ImportGraph'})  # Mathlib and its own dependencies
if bad:
    print('BLOCKER: closure needs packages other than Mathlib:', bad); sys.exit(3)
for m in seen:
    rel = m.replace('.', '/') + '.lean'
    os.makedirs(os.path.dirname(os.path.join(dst, rel)), exist_ok=True)
    shutil.copy(where[m], os.path.join(dst, rel))
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
  # The outside project's own Lean options (autoImplicit etc.), not ours: a proof written with
  # autoImplicit on fails to elaborate with it off (T2 run 45869342368: "Unknown identifier X").
  python3 - "$SRC" <<'PY2'
import os, re, sys
src = sys.argv[1]
t, l = os.path.join(src, 'lakefile.toml'), os.path.join(src, 'lakefile.lean')
opts = []
if os.path.exists(t):
    txt = open(t, encoding='utf-8').read()
    m = re.search(r'^\[leanOptions\]\s*\n(.*?)(?=^\[|\Z)', txt, flags=re.M | re.S)
    if m:
        opts = [ln for ln in m.group(1).splitlines() if '=' in ln and not ln.strip().startswith('#')]
    # Top-level moreLeanArgs (e.g. --tstack=400000 in target R's editions): without it deep
    # elaboration can overflow the stack and a sound proof would FAIL on our side (run 2026-11-27T0628Z).
    head = re.split(r'^\[', txt, maxsplit=1, flags=re.M)[0]
    mla = re.search(r'^moreLeanArgs\s*=\s*\[.*?\]\s*$', head, flags=re.M)
    if mla:
        print(mla.group(0))
elif os.path.exists(l):
    txt = open(l, encoding='utf-8').read()
    for name, val in re.findall(r'⟨`([\w.]+)\s*,\s*([^⟩]+)⟩', txt):
        val = val.strip()
        opts.append(f'"{name}" = {val}' if val in ('true', 'false') or val.isdigit() else f'"{name}" = "{val}"')
print('[leanOptions]')
for o in opts:
    print(o)
PY2
  echo '[[require]]'
  echo 'name = "mathlib"'
  echo 'git = "https://github.com/leanprover-community/mathlib4.git"'
  echo "rev = \"$MATHLIB_REV\""
  for l in $(cat closure_libs.txt) $(for e in ${EXTRA:-}; do echo "${e%%=*}" | cut -d. -f1; done | sort -u); do
    echo '[[lean_lib]]'; echo "name = \"$l\""; done
} > lakefile.toml
[ -d .lake/packages/mathlib ] || lake update > lake_update.log 2>&1
lake exe cache get > cache.log 2>&1 || true

# leanchecker (step 4), as a function so that it can also run alone on a slice of the closure:
# Each leanchecker invocation re-imports the environment of every module it is given, so batching saves
# little; time is per module (S-egyptian on GitHub: ≈41 s/module; T1 Navier–Stokes ≈6.5 s/module). So
# batches (LC_BATCH, default 2) run LC_JOBS at a time (default: number of cores).
# Memory history: one process over a whole closure was OOM-killed at 4.5 GB in the session sandbox
# (58 modules); a T1 job in batches of 20 lost its runner (run 45890308119, no log). Two guards: every
# leanchecker process raises its own oom_score_adj to 1000, so under memory pressure the kernel kills it
# and not the runner; a batch that fails is replayed again one module per process, one at a time, and only
# a failure there fails the judge (a kernel error fails both ways; a memory kill only the batch).
run_leanchecker() {
  LC_BATCH=${LC_BATCH:-2}
  LC_JOBS=${LC_JOBS:-$(nproc)}
  ALL_MODS="$*"
  LC_TOTAL=$(printf '%s\n' $ALL_MODS | wc -l)
  mkdir -p lc_logs; : > lc_failed_batches.txt; : > lc_done.txt
  lc_batch() {
    local log="lc_logs/$1.log"
    if bash -c 'echo 1000 > /proc/self/oom_score_adj 2>/dev/null; exec lake env leanchecker "$@"' _ "$@" > "$log" 2>&1; then :
    else echo "exit $? on batch: $*" >> "$log"; echo "$*" >> lc_failed_batches.txt; fi
    echo "$*" >> lc_done.txt
    echo "leanchecker: $(wc -w < lc_done.txt)/$LC_TOTAL modules; $(free -m | awk '/^Mem:/{print "mem used " $3 " MB of " $2}')"
  }
  export -f lc_batch; export LC_TOTAL
  printf '%s\n' $ALL_MODS | xargs -n "$LC_BATCH" -P "$LC_JOBS" bash -c 'lc_batch "$@"' _
  LC_FAIL=0; LC_RETRIED=0
  for m in $(cat lc_failed_batches.txt); do
    LC_RETRIED=$((LC_RETRIED + 1))
    bash -c 'echo 1000 > /proc/self/oom_score_adj 2>/dev/null; exec lake env leanchecker "$@"' _ "$m" > "lc_logs/retry_$m.log" 2>&1 || {
      echo "FAIL module: $m (exit $?)"; tail -5 "lc_logs/retry_$m.log"; LC_FAIL=$((LC_FAIL + 1)); }
  done
  cat lc_logs/*.log > leanchecker.log
  [ "$(wc -w < lc_done.txt)" = "$LC_TOTAL" ] || { echo "FAIL: leanchecker ran $(wc -w < lc_done.txt) of $LC_TOTAL modules"; exit 1; }
  [ "$LC_FAIL" = 0 ] || { echo "FAIL: leanchecker ($LC_FAIL modules)"; exit 1; }
  echo "leanchecker: replayed $LC_TOTAL modules, batches of $LC_BATCH, $LC_JOBS at a time ($LC_RETRIED re-run singly after a batch failure): OK"
}

# Shard mode (LC_SHARD=k/n, Alexander 2026-11-26: "shard leanchecker over several GitHub jobs"): rebuild
# (a no-op on the build directory restored from the replay job), then leanchecker on modules number
# k, k+n, k+2n, ... of the closure (plus the program's extra modules), and stop. Compare, axioms and nanoda
# are the replay job's; a shard only adds the second kernel's replay of its slice.
if [ -n "${LC_SHARD:-}" ]; then
  k=${LC_SHARD%/*}; n=${LC_SHARD#*/}
  for e in ${EXTRA:-}; do
    mod=${e%%=*}; file=${e#*=}; rel=${mod//.//}.lean
    mkdir -p "$(dirname "$rel")"; cp "$OLDPWD_SRC/$file" "$rel" 2>/dev/null || cp "$file" "$rel"
  done
  ALL=$(cat closure_modules.txt; for e in ${EXTRA:-}; do echo "${e%%=*}"; done)
  # shellcheck disable=SC2086
  lake build $ALL > build.log 2>&1 || { tail -40 build.log; echo "FAIL: build"; exit 1; }
  echo "shard build: $(grep -c 'Built ' build.log || true) modules (re)built, the rest from the restored build"
  SLICE=$(printf '%s\n' $ALL | awk -v k="$k" -v n="$n" '(NR - 1) % n == k - 1')
  echo "leanchecker shard $k/$n: $(printf '%s\n' $SLICE | wc -l) of $(printf '%s\n' $ALL | wc -l) modules"
  # shellcheck disable=SC2086
  [ -z "$SLICE" ] || run_leanchecker $SLICE
  echo "== leanchecker shard $k/$n PASSED"
  exit 0
fi

# 1-2. compare challenge declarations with the solution's; axioms of the targets
lake build "$SOL" "$CHAL" > build.log 2>&1 || { tail -40 build.log; echo "FAIL: build"; exit 1; }
lake env lean --run "$HERE/compare_decls.lean" "$CHAL" "$SOL" "${THMS[@]}" > compare.log 2>&1 || {
  grep -v '^  •' compare.log | tail -40; echo "FAIL: compare"; exit 1; }
grep -v '^  •' compare.log
echo "${THMS[*]}" > target_names.txt
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
  # blind readings are statements with `sorry` by design: no axiom check; every other extra module
  # (closures, pins) must print its axioms and they must be standard
  case "$mod" in
    Readings.*) ;;
    *) python3 "$HERE/check_axioms.py" "check_$mod.log" || { echo "FAIL: $mod axioms"; exit 1; } ;;
  esac
  grep "depends on axioms" "check_$mod.log" || true
done
EXTRA_LIBS=$(echo "$EXTRA_LIBS" | tr ' ' '\n' | sort -u | tr '\n' ' ')
# 3. nanoda (optional) - runs BEFORE leanchecker so a leanchecker crash (memory, time) can never stop the
#    independent check from reporting (Alexander, 2026-11-26: T1 verdict by morning whatever leanchecker does)
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
  lake env "$L4E/.lake/build/bin/lean4export" "$SOL" -- $(cat target_names.txt) > export.ndjson
  cat > nanoda.json <<CFG
{ "export_file_path": "export.ndjson", "use_stdin": false,
  "permitted_axioms": ["propext", "Classical.choice", "Quot.sound"],
  "unpermitted_axiom_hard_error": true, "nat_extension": true, "string_extension": true,
  "print_success_message": true }
CFG
  "$NAN/target/release/nanoda_bin" nanoda.json > nanoda.log 2>&1 || { tail -20 nanoda.log; echo "FAIL: nanoda"; exit 1; }
  tail -3 nanoda.log; echo "nanoda: OK ($(wc -l < export.ndjson) export lines)"; echo "== RESULT so far: match, axioms and nanoda PASSED (leanchecker follows)"
fi
# 4. leanchecker on every copied module and the program's extra modules (run_leanchecker, defined above)
if [ "${LC_SKIP:-0}" = 1 ]; then
  echo "leanchecker: not run in this job (LC_SKIP=1); the workflow runs it in LC_SHARD jobs over the same build"
else
  run_leanchecker $(cat closure_modules.txt; for e in ${EXTRA:-}; do echo "${e%%=*}"; done)
fi
# 4b. coverage of the blind readings by the closures (informative: a verdict is DONE only at full coverage)
READ_FILES=""; CLOS_FILES=""
for e in ${EXTRA:-}; do
  mod=${e%%=*}; rel=${mod//.//}.lean
  case "$mod" in Readings.*) READ_FILES="$READ_FILES $rel" ;; Closure.*) CLOS_FILES="$CLOS_FILES $rel" ;; esac
done
COV="COMPLETE"
[ -n "$READ_FILES" ] || COV="NONE (no blind reading supplied)"
for r in $READ_FILES; do
  # shellcheck disable=SC2086
  python3 "$HERE/coverage.py" "$r" $CLOS_FILES || { echo "coverage: $r has UNCOVERED theorems (see above)"; COV="INCOMPLETE"; }
done
# 5. advisory scan
python3 "$HERE/scan_escapes.py" "$WORK" "$SOL" | tail -2
echo "== external replay PASSED: $SOL proves $CHAL (${THMS[*]})"
# The pass above is about the outside proof only. A DONE also needs every theorem of the blind reading
# closed (red team, run 2026-11-26T1529Z: a sorry'd "closure" placed under a Readings.* name passed the
# replay with this line alone; coverage counted it UNCOVERED, so no false DONE, but the line misled).
echo "== coverage of the blind readings by Closure.* modules: $COV (a DONE needs COMPLETE)"
