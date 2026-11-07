import Export
open Lean

/-!
Sharded lean4export driver (part of the judge, annex 39.5; run 2026-11-07T0428Z, see LEDGER).

Identical to lean4export's own `Main.lean` (pinned tag v4.35.0) in what it exports for each constant
(`initState`, `dumpMetadata`, `dumpConstant`, the same per-constant reset of `noMDataExprs`) and in which
constants exist (`env.constants`, non-internal, exactly the default list of `Main.lean`). The only
difference: shard `i` of `k` exports only the constants whose defining module `m` satisfies
`shardOf m k = i` (plus, as always, everything they depend on). The shards partition the default list,
so the union of the `k` exports covers every constant of the unsharded export, and each shard is a
self-contained environment that nanoda checks on its own. Why: one export of all of `Checked` grew to
135 M lines and took 5 h 06 min on the CI runner (run 42306265048), past the 6-hour job limit once the
build is added; per-shard exporter state stays small.

Usage: exportshard <Module> <i> <k>        (prints the export to stdout, counts to stderr)
-/

/-- FNV-1a over the module name's string: deterministic across processes and machines. -/
def shardOf (m : Name) (k : Nat) : Nat :=
  let h := m.toString.foldl (fun (h : UInt64) c => (h ^^^ c.toNat.toUInt64) * 1099511628211) 14695981039346656037
  (h % k.toUInt64).toNat

def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let [mod, iS, kS] := args | IO.eprintln "usage: exportshard <Module> <i> <k>"; return 2
  let some i := iS.toNat? | return 2
  let some k := kS.toNat? | return 2
  if k == 0 || i ≥ k then IO.eprintln "need 0 ≤ i < k"; return 2
  let env ← importModules #[{ module := Syntax.decodeNameLit ("`" ++ mod) |>.get! }] {}
  let all := env.constants.toList.map Prod.fst |>.filter (!·.isInternal)
  let modOf (c : Name) : Name :=
    match env.getModuleIdxFor? c with
    | some idx => env.header.moduleNames[idx.toNat]!
    | none => mod.toName  -- constants added outside any imported module (none expected)
  let mine := all.filter (fun c => shardOf (modOf c) k == i)
  IO.eprintln s!"exportshard: shard {i} of {k}: {mine.length} of {all.length} constants"
  M.run env do
    let _ ← initState env []
    dumpMetadata
    for c in mine do
      modify (fun st => { st with noMDataExprs := {} })
      dumpConstant c
  return 0
