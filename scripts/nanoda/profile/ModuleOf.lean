import Lean
open Lean

/-! Measurement only (run 2026-11-20T1228Z; never used by the judge): print `<module> <constant>` for every
constant of the environment of `Checked` (names unescaped, as nanoda prints them), so that the per-declaration
times of `patch_nanoda_profile.py` can be summed per module by `aggregate.py`.
Usage: `lake env lean --run scripts/nanoda/profile/ModuleOf.lean > modof.txt` -/

def main : IO Unit := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `Checked }] {}
  let out ← IO.getStdout
  for (n, _) in env.constants.toList do
    match env.getModuleIdxFor? n with
    | some idx => out.putStrLn s!"{env.header.moduleNames[idx.toNat]!} {n.toString (escape := false)}"
    | none => pure ()
