#!/usr/bin/env bash
# Independent type check of the `Checked` library with nanoda (a Lean type checker
# written separately from Lean's own kernel). Adapted from leanprover/lean-action v1.7.0
# scripts/run_nanoda.sh, which could not detect our module name. Part of the judge (annex 39.5).
set -euo pipefail
MODULE_NAME="Checked"
rm -rf _lean4export _nanoda_lib _nanoda_export.txt _nanoda_config.json
git clone --depth 1 https://github.com/leanprover/lean4export.git _lean4export
cp lean-toolchain _lean4export/
(cd _lean4export && lake build)
git clone --depth 1 --branch debug https://github.com/ammkrn/nanoda_lib.git _nanoda_lib
(cd _nanoda_lib && cargo build --release)
lake env _lean4export/.lake/build/bin/lean4export "$MODULE_NAME" > _nanoda_export.txt
echo "Export lines: $(wc -l < _nanoda_export.txt)"
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
echo "nanoda: Checked passed"
