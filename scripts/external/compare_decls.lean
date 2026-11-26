import Lean
open Lean

/-!
Comparator-style check of an outside result (external test; run 2026-11-26T1529Z, after the
diagnosis of the target-1 replay failure: copying a challenge's `structure`s into another namespace
makes new types, so a challenge must be compared, not copied).

Usage: `lake env lean --run scripts/external/compare_decls.lean <ChallengeModule> <SolutionModule> <thm>...`

Loads the challenge module and the solution module into two separate environments and checks, for
every constant DECLARED IN the challenge module:
- it exists in the solution environment with the same kind, universe parameters and type (Expr
  equality up to binder names);
- if it is a definition (or opaque), the same value; if an inductive type, the same parameters,
  constructors and recursor types (constructors and recursors are constants of the module and are
  compared by the same loop);
- if it is one of the named target theorems, the challenge proof is `sorry` and is not compared:
  only its statement (type) must be identical;
- other theorems (helpers proved in the challenge): statement identical.
Then it checks that every target theorem of the solution environment uses only the axioms
propext, Classical.choice, Quot.sound. Exit 0 iff everything holds; one line per failure.
Statement identity is by expression equality on the solution's own definitions, exactly the question
leanprover/comparator answers, without its sandbox.
-/

def kindOf : ConstantInfo → String
  | .axiomInfo _ => "axiom" | .defnInfo _ => "def" | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque" | .quotInfo _ => "quot" | .inductInfo _ => "inductive"
  | .ctorInfo _ => "ctor" | .recInfo _ => "rec"

unsafe def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  match args with
  | chal :: sol :: thms =>
    let chal := chal.toName
    let sol := sol.toName
    let thms := thms.map String.toName
    -- Only the solution is imported as an environment (one Mathlib in memory: two environments
    -- were OOM-killed in a 5 GB sandbox); the challenge's own declarations are read from its .olean
    -- without importing its dependencies (constants refer to Mathlib by name only).
    let envS ← importModules #[{ module := sol }] {} (trustLevel := 1024)
    let (modC, _) ← readModuleData (← findOLean chal)
    let consts := modC.constants
    let mut bad := 0
    let mut n := 0
    for ci in consts do
      let c := ci.name
      n := n + 1
      match envS.find? c with
      | none => IO.println s!"MISSING in solution: {c}"; bad := bad + 1
      | some si =>
        if kindOf ci != kindOf si then
          IO.println s!"KIND differs: {c} ({kindOf ci} vs {kindOf si})"; bad := bad + 1
        else if ci.levelParams != si.levelParams then
          IO.println s!"UNIVERSES differ: {c}"; bad := bad + 1
        else if !(ci.type == si.type) then
          IO.println s!"TYPE differs: {c}"; bad := bad + 1
        else
          match ci, si with
          | .defnInfo a, .defnInfo b =>
            if !(a.value == b.value) then IO.println s!"VALUE differs: {c}"; bad := bad + 1
          | .opaqueInfo a, .opaqueInfo b =>
            if !(a.value == b.value) then IO.println s!"VALUE differs: {c}"; bad := bad + 1
          | .inductInfo a, .inductInfo b =>
            if a.numParams != b.numParams || a.numIndices != b.numIndices || a.ctors != b.ctors then
              IO.println s!"INDUCTIVE differs: {c}"; bad := bad + 1
          | _, _ => pure ()
    IO.println s!"compared {n} challenge declarations: {bad} differences"
    -- target theorems: present in both with identical statements (checked above when declared in
    -- the challenge module); now their axioms in the solution environment
    for t in thms do
      if !(consts.any (·.name == t)) then IO.println s!"TARGET not in challenge: {t}"; bad := bad + 1
      match envS.find? t with
      | none => IO.println s!"TARGET not in solution: {t}"; bad := bad + 1
      | some _ =>
        let (axs, _) ← (collectAxioms t : CoreM (Array Name)).toIO
          { fileName := "<compare_decls>", fileMap := default } { env := envS }
        let ax := axs.toList
        let extra := ax.filter fun a => !([``propext, ``Classical.choice, ``Quot.sound].contains a)
        IO.println s!"'{t}' depends on axioms: {ax}"
        if extra.length != 0 then IO.println s!"NON-STANDARD AXIOMS {t}: {extra}"; bad := bad + 1
    IO.println (if bad == 0 then "COMPARE OK" else s!"COMPARE FAILED: {bad}")
    return (if bad == 0 then 0 else 1)
  | _ => IO.eprintln "usage: compare_decls <Challenge> <Solution> <thm>..."; return 2
