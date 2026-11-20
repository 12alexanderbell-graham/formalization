#!/usr/bin/env bash
# Independent type check of the `Checked` library with nanoda, shard I of K (part of the judge, annex 39.5;
# run 2026-11-07T0428Z, see LEDGER). Same pinned lean4export and nanoda revisions and the same nanoda
# configuration as scripts/nanoda_checked.sh (not run by CI) except the worker count (below); the export is produced by scripts/nanoda/ShardMain.lean, which
# exports exactly lean4export's default constant list of `Checked` restricted to the constants whose module
# falls in shard I (FNV-1a hash of the module name mod K), each with all its dependencies. The K shards
# partition that list, so K green shard jobs check every constant the unsharded export checked.
# Workers (run 2026-11-19T2028Z, annex LIV, integrity event 39.5; see LEDGER): nanoda checked every declaration on one
# thread (num_threads unset), so the slowest shard took 3 h 16 min (CI 44521044439, shard 1: 235,376 declarations)
# on a 4-core runner while three cores idled, and every promotion waited on it. nanoda_lib's own option
# `num_threads` (pinned revision: each worker takes the next declaration index until all are taken; a failing check
# panics in its worker and the panic is re-raised on join, exit 101) now uses every core (NANODA_THREADS, default
# nproc). The same declarations are checked by the same checker; before the shard, the planted controls of
# scripts/nanoda/controls/ run with the same configuration: the good export must pass, the export with one false
# literal must be rejected. Each phase prints its wall time (`nanoda-time ...`) for balancing the shards.
# Assumed theorems of other shards (run 2026-11-20T1428Z, annex LIV, integrity event 39.5; see LEDGER and the doc of
# scripts/nanoda/ShardMain.lean): the per-declaration profile (CI 44736861516) showed about half of every shard's work
# was re-checking other shards' Checked proofs reached as dependencies. The export now gives a non-internal theorem of
# another shard's Checked module as an axiom (same name and type), lists its name in _nanoda_assumed.txt, and nanoda
# admits exactly those names besides the four standard axioms (permitted_axioms). Each such theorem is exported in
# full and checked in its own shard, so the four green shards still check every declaration of the default list.
# Tested on Init (scripts/nanoda/assume_test/): the union of fully exported declarations is identical with and
# without assumption, every assumed theorem is a full theorem of another shard, all shards pass.
# Usage: scripts/nanoda_shard.sh I K
set -euo pipefail
I="$1"; K="$2"
THREADS="${NANODA_THREADS:-$(nproc)}"
MODULE_NAME="Checked"
rm -rf _lean4export _nanoda_lib _nanoda_export.txt _nanoda_assumed.txt _nanoda_config.json _nanoda_ctl_*.json _nanoda_ctl_*.out
LEAN4EXPORT_REV="v4.35.0"   # 5a9a355dc6c5fd82b69058d433e2ae2e8dfbf8fe
NANODA_REV="8de7e0c4ed3052745a7f8725164efd9e76d84c56"   # nanoda_lib master, 2026-10-29
git clone --depth 1 --branch "$LEAN4EXPORT_REV" https://github.com/leanprover/lean4export.git _lean4export
cp lean-toolchain _lean4export/
cp scripts/nanoda/ShardMain.lean _lean4export/ShardMain.lean
printf '\n[[lean_exe]]\nname = "exportshard"\nroot = "ShardMain"\nsupportInterpreter = true\n' >> _lean4export/lakefile.toml
(cd _lean4export && lake build exportshard)
git clone https://github.com/ammkrn/nanoda_lib.git _nanoda_lib
(cd _nanoda_lib && git checkout --quiet "$NANODA_REV")
(cd _nanoda_lib && cargo build --release)
write_config() {  # write_config <export file> <config file> [<assumed-names file>]: the one nanoda configuration
# of this script; the optional third argument adds the names of the theorems the export assumes from other shards
PERMITTED=$(python3 -c 'import json, sys
names = ["propext", "Classical.choice", "Quot.sound", "Lean.trustCompiler"]
if len(sys.argv) > 1:
    names += [l.rstrip("\n") for l in open(sys.argv[1], encoding="utf-8") if l.strip()]
print(json.dumps(names))' ${3:+"$3"})
cat > "$2" <<CFG
{
    "export_file_path": "$1",
    "use_stdin": false,
    "permitted_axioms": $PERMITTED,
    "unpermitted_axiom_hard_error": false,
    "nat_extension": true,
    "string_extension": true,
    "print_success_message": true,
    "num_threads": $THREADS
}
CFG
}
NANODA=_nanoda_lib/target/release/nanoda_bin
# Planted controls (scripts/nanoda/controls/README.md), same configuration and worker count as the shard.
write_config scripts/nanoda/controls/ndctl_good.txt _nanoda_ctl_good.json
write_config scripts/nanoda/controls/ndctl_bad.txt _nanoda_ctl_bad.json
if ! "$NANODA" _nanoda_ctl_good.json > _nanoda_ctl_good.out 2>&1; then
  cat _nanoda_ctl_good.out; echo "nanoda control: the good planted export was rejected"; exit 1
fi
head -3 _nanoda_ctl_good.out
if "$NANODA" _nanoda_ctl_bad.json > _nanoda_ctl_bad.out 2>&1; then
  cat _nanoda_ctl_bad.out; echo "nanoda control: the planted export with a false literal PASSED; the judge is not checking"; exit 1
fi
echo "nanoda control: the planted false export was rejected as required ($(grep -m1 -o 'panicked at.*' _nanoda_ctl_bad.out || head -c 200 _nanoda_ctl_bad.out))"
t0=$(date +%s)
lake env _lean4export/.lake/build/bin/exportshard "$MODULE_NAME" "$I" "$K" _nanoda_assumed.txt > _nanoda_export.txt
t1=$(date +%s)
echo "Export lines: $(wc -l < _nanoda_export.txt)"
echo "Export header: $(head -c 300 _nanoda_export.txt)"
echo "nanoda-time export $((t1 - t0)) s shard $I of $K"
echo "Assumed theorems of other shards (checked there): $(wc -l < _nanoda_assumed.txt)"
write_config _nanoda_export.txt _nanoda_config.json _nanoda_assumed.txt
echo "nanoda workers: $THREADS (nproc $(nproc))"
"$NANODA" _nanoda_config.json
t2=$(date +%s)
echo "nanoda-time check $((t2 - t1)) s shard $I of $K workers $THREADS"
echo "nanoda: Checked shard $I of $K passed"
