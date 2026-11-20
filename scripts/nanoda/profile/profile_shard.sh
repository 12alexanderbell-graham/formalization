#!/usr/bin/env bash
# Measurement only (run 2026-11-20T1228Z; not part of the judge, run by .github/workflows/nanoda-profile.yml on
# workflow_dispatch): the export of scripts/nanoda_shard.sh (same pinned lean4export, same ShardMain, same
# assignment) checked by the same pinned nanoda revision patched to time each declaration
# (patch_nanoda_profile.py), then summed per module (ModuleOf.lean, aggregate.py). Output: _ndprof/shard<I>.txt
# (per-module seconds of worker time) and _ndprof/shard<I>_raw.txt (the ndprof lines).
# Usage: scripts/nanoda/profile/profile_shard.sh I K
set -euo pipefail
I="$1"; K="$2"
THREADS="${NANODA_THREADS:-$(nproc)}"
export NANODA_PROFILE_MIN_US="${NANODA_PROFILE_MIN_US:-5000}"
rm -rf _lean4export _nanoda_lib _nanoda_export.txt _nanoda_config.json _ndprof
mkdir -p _ndprof
LEAN4EXPORT_REV="v4.35.0"
NANODA_REV="8de7e0c4ed3052745a7f8725164efd9e76d84c56"
git clone --depth 1 --branch "$LEAN4EXPORT_REV" https://github.com/leanprover/lean4export.git _lean4export
cp lean-toolchain _lean4export/
cp scripts/nanoda/ShardMain.lean _lean4export/ShardMain.lean
printf '\n[[lean_exe]]\nname = "exportshard"\nroot = "ShardMain"\nsupportInterpreter = true\n' >> _lean4export/lakefile.toml
(cd _lean4export && lake build exportshard)
git clone https://github.com/ammkrn/nanoda_lib.git _nanoda_lib
(cd _nanoda_lib && git checkout --quiet "$NANODA_REV")
python3 scripts/nanoda/profile/patch_nanoda_profile.py _nanoda_lib
(cd _nanoda_lib && cargo build --release)
lake env lean --run scripts/nanoda/profile/ModuleOf.lean > _ndprof/modof.txt
echo "constants with modules: $(wc -l < _ndprof/modof.txt)"
t0=$(date +%s)
lake env _lean4export/.lake/build/bin/exportshard Checked "$I" "$K" _ndprof/assumed.txt > _nanoda_export.txt
t1=$(date +%s)
echo "nanoda-time export $((t1 - t0)) s shard $I of $K"
# the judge's own export since run 2026-11-20T1428Z: theorems of other shards' Checked modules assumed (ShardMain doc)
PERMITTED=$(python3 -c 'import json, sys
print(json.dumps(["propext", "Classical.choice", "Quot.sound", "Lean.trustCompiler"] + [l.rstrip("\n") for l in open(sys.argv[1], encoding="utf-8") if l.strip()]))' _ndprof/assumed.txt)
cat > _nanoda_config.json <<CFG
{
    "export_file_path": "_nanoda_export.txt",
    "use_stdin": false,
    "permitted_axioms": $PERMITTED,
    "unpermitted_axiom_hard_error": false,
    "nat_extension": true,
    "string_extension": true,
    "print_success_message": true,
    "num_threads": $THREADS
}
CFG
_nanoda_lib/target/release/nanoda_bin _nanoda_config.json 2> _ndprof/shard${I}_raw.txt
t2=$(date +%s)
echo "nanoda-time check $((t2 - t1)) s shard $I of $K workers $THREADS (profiled)"
grep -v '^ndprof ' _ndprof/shard${I}_raw.txt | head -20 || true
python3 scripts/nanoda/profile/aggregate.py _ndprof/shard${I}_raw.txt _ndprof/modof.txt > _ndprof/shard${I}.txt
head -40 _ndprof/shard${I}.txt
# (run 2026-11-20T1428Z: under pipefail, head closing the pipe failed the step after every output was written)
grep "^ndprof " _ndprof/shard${I}_raw.txt | sort -rn -k2 | head -40 || true
