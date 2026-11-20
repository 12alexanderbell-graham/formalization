#!/usr/bin/env bash
# Test of the assumed-theorem export of scripts/nanoda/ShardMain.lean (run 2026-11-20T1428Z), on Lean's own `Init`
# instead of `Checked` (the assumed root is switched by sed in a copy; nothing else changes). For each of 4 shards it
# exports with and without the fourth argument, checks every export with the pinned nanoda (old: the four standard
# axioms; new: plus the shard's assumed names), and runs coverage.py: the union over shards of fully exported
# declarations must be the same both ways, and every assumed theorem must be a full theorem of another shard.
# Run 2026-11-20T1428Z (2 cores): all 8 nanoda runs pass; 57,911 full declarations both ways, 0 missing, 0 extra;
# 2,113-2,472 assumed per shard, 0 not fully exported elsewhere; nanoda 57 s -> 31 s summed over the shards.
# Usage: scripts/nanoda/assume_test/run_init_test.sh <lean4export v4.35.0 checkout> <built nanoda_bin> <work dir>
set -euo pipefail
EXP="$1"; NANODA="$2"; W="$3"; HERE="$(cd "$(dirname "$0")" && pwd)"
sed 's/getRoot == `Checked/getRoot == `Init/' "$HERE/../ShardMain.lean" > "$EXP/ShardMain.lean"
grep -q exportshard "$EXP/lakefile.toml" || printf '\n[[lean_exe]]\nname = "exportshard"\nroot = "ShardMain"\nsupportInterpreter = true\n' >> "$EXP/lakefile.toml"
(cd "$EXP" && lake build exportshard)
mkdir -p "$W"
for i in 0 1 2 3; do
  (cd "$EXP" && lake env .lake/build/bin/exportshard Init $i 4 > "$W/old$i.txt" && lake env .lake/build/bin/exportshard Init $i 4 "$W/assumed$i.txt" > "$W/new$i.txt")
  for v in old new; do
    python3 - "$W" $i $v <<'PY'
import json, sys
w, i, v = sys.argv[1:]
ax = ["propext", "Classical.choice", "Quot.sound", "Lean.trustCompiler"]
if v == "new":
    ax += [l.strip() for l in open(f"{w}/assumed{i}.txt") if l.strip()]
json.dump({"export_file_path": f"{w}/{v}{i}.txt", "use_stdin": False, "permitted_axioms": ax,
           "unpermitted_axiom_hard_error": False, "nat_extension": True, "string_extension": True,
           "print_success_message": True, "num_threads": 2}, open(f"{w}/{v}{i}.json", "w"))
PY
    "$NANODA" "$W/$v$i.json" | head -c 200; echo
  done
done
(cd "$W" && python3 "$HERE/coverage.py")
