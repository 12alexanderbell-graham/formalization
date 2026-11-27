# Red team material (record: `validation/EXTERNAL_REDTEAM.md`)

- `mk.py`: from `base/` (a copy of the S-egyptian outside sources: `OAI/`, `ComparatorChallenges/`,
  `lean-toolchain`, `lake-manifest.json`, `lakefile.toml` with the outside leanOptions) makes one copy per
  planted defect (P0–P5, P7_P8_extras).
- `run.sh <variant> [EXTRA...]`: runs `scripts/external/replay.sh` on a variant with `LC_SKIP=1 NANODA=0`
  into `$WORK` (a replay project of S-egyptian, reused so that only changed modules rebuild).
- `extras/`: the planted closure and reading modules for P7, P7b, P8, P8b.
- `results.txt`: the result lines of every variant and the nanoda run on P3.
