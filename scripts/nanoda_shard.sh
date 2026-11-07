#!/usr/bin/env bash
# Independent type check of the `Checked` library with nanoda, shard I of K (part of the judge, annex 39.5;
# run 2026-11-07T0428Z, see LEDGER). Same pinned lean4export and nanoda revisions and the same nanoda
# configuration as scripts/nanoda_checked.sh; the export is produced by scripts/nanoda/ShardMain.lean, which
# exports exactly lean4export's default constant list of `Checked` restricted to the constants whose module
# falls in shard I (FNV-1a hash of the module name mod K), each with all its dependencies. The K shards
# partition that list, so K green shard jobs check every constant the unsharded export checked.
# Usage: scripts/nanoda_shard.sh I K
set -euo pipefail
I="$1"; K="$2"
MODULE_NAME="Checked"
rm -rf _lean4export _nanoda_lib _nanoda_export.txt _nanoda_config.json
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
lake env _lean4export/.lake/build/bin/exportshard "$MODULE_NAME" "$I" "$K" > _nanoda_export.txt
echo "Export lines: $(wc -l < _nanoda_export.txt)"
echo "Export header: $(head -c 300 _nanoda_export.txt)"
cat > _nanoda_config.json <<CFG
{
    "export_file_path": "_nanoda_export.txt",
    "use_stdin": false,
    "permitted_axioms": ["propext", "Classical.choice", "Quot.sound", "Lean.trustCompiler"],
    "unpermitted_axiom_hard_error": false,
    "nat_extension": true,
    "string_extension": true,
    "print_success_message": true
}
CFG
_nanoda_lib/target/release/nanoda_bin _nanoda_config.json
echo "nanoda: Checked shard $I of $K passed"
