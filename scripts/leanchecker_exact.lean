import LeanChecker
open Lean

/-!
Exact-module kernel replay with the toolchain's own `replayFromImports` (LeanChecker.lean, the function the
`leanchecker` executable calls for each module). Part of the judge (annex 39.5; run 2026-11-19T0628Z, see LEDGER).

Why: `leanchecker M` replays every module whose name has `M` as a prefix (LeanChecker.lean, `checkOlean`:
`target.isPrefixOf m`). The root module `Checked` (Checked.lean) is a name prefix of every module of the library, so the
leanchecker shard holding it replayed the whole library a second time (2026-11-19: one group of eight modules took
10,159 s of a 14,091-s shard in run 44424316043; shard 0 of run 44451569867 past 3 h while the others took 37-49 min).
This file replays exactly the modules named in `LEANCHECKER_EXACT` (space-separated) and nothing else; every module is
still replayed by exactly one shard, so the union of the shards is what `leanchecker Checked` replays.

Usage: LEANCHECKER_EXACT='Checked' lake env lean scripts/leanchecker_exact.lean   (fails on any rejected declaration)
-/

unsafe def leancheckerExactRun : IO Unit := do
  initSearchPath (← findSysroot)
  let some s := (← IO.getEnv "LEANCHECKER_EXACT") | throw (IO.userError "LEANCHECKER_EXACT is not set")
  let mods := (s.splitOn " ").filter (· ≠ "")
  if mods.isEmpty then throw (IO.userError "LEANCHECKER_EXACT names no module")
  for m in mods do
    let n := m.toName
    if n.isAnonymous then throw (IO.userError s!"Could not resolve module: {m}")
    replayFromImports n
    IO.println s!"leanchecker-exact replayed {m}"

#eval leancheckerExactRun
