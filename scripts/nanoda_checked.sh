#!/usr/bin/env bash
# Independent type check of the `Checked` library with nanoda (a Lean type checker
# written separately from Lean's own kernel). Adapted from leanprover/lean-action v1.7.0
# scripts/run_nanoda.sh, which could not detect our module name. Part of the judge (annex 39.5).
set -euo pipefail
# Axiom settings match lean-action upstream: nanoda is the independent type checker here.
# The axiom judge for our own declarations is axiom-audit (allowlist: propext, Classical.choice, Quot.sound).
MODULE_NAME="Checked"
rm -rf _lean4export _nanoda_lib _nanoda_export.txt _nanoda_config.json
# Pinned (run 2026-10-30T0220Z repair): lean4export tag matching our toolchain (HEAD moved to
# v4.36.0-rc1), and nanoda_lib master, which reads lean4export's JSON format 3.1.x (the old
# `debug` branch, dated 2025-10, could not parse it: "invalid digit found in string").
LEAN4EXPORT_REV="v4.35.0"   # 5a9a355dc6c5fd82b69058d433e2ae2e8dfbf8fe
NANODA_REV="8de7e0c4ed3052745a7f8725164efd9e76d84c56"   # nanoda_lib master, 2026-10-29
git clone --depth 1 --branch "$LEAN4EXPORT_REV" https://github.com/leanprover/lean4export.git _lean4export
cp lean-toolchain _lean4export/
(cd _lean4export && lake build)
git clone https://github.com/ammkrn/nanoda_lib.git _nanoda_lib
(cd _nanoda_lib && git checkout --quiet "$NANODA_REV")
(cd _nanoda_lib && cargo build --release)
lake env _lean4export/.lake/build/bin/lean4export "$MODULE_NAME" > _nanoda_export.txt
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
echo "nanoda: Checked passed"
