# Planted controls of the nanoda judge

Run 2026-11-19T2028Z (annex LIV, integrity event 39.5; see LEDGER). `scripts/nanoda_shard.sh` runs nanoda with
several checking workers (`num_threads`, nanoda_lib's own option). Before checking its shard it runs nanoda, with
exactly the shard's configuration, on two planted exports and fails unless:

- `ndctl_good.txt` (lean4export v4.35.0 of `NdCtl.lean`, the five `ndctl_*` constants and their dependencies) passes;
- `ndctl_bad.txt` (the same file with one literal changed: line 2463, `natVal` 21 → 22, so `ndctl_d : ndctl_f 7 = 22`
  carries the proof `rfl` of `ndctl_f 7 = 21`) is rejected with a nonzero exit.

So a configuration in which a worker's failure is not reported as a failure of the job cannot pass.

Regenerate (only if the toolchain or the export format changes):

```
lean -o NdCtl.olean NdCtl.lean
LEAN_PATH=$(lean --print-libdir):. <lean4export>/.lake/build/bin/lean4export NdCtl -- ndctl_a ndctl_b ndctl_c ndctl_d ndctl_f > ndctl_good.txt
sed 's/"natVal":"21"}/"natVal":"22"}/' ndctl_good.txt > ndctl_bad.txt   # exactly one line differs
```

Measured locally (run 2026-11-19T2028Z, nanoda_lib 8de7e0c): good passes with 1 and 4 workers (101 declarations);
bad fails with exit 101 with 1 and 4 workers (`assertion failed: self.def_eq(u, v)` in a worker thread).
