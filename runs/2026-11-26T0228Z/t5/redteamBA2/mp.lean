/-! BA2 metaprogram: copy a program proof into the closure module with every program theorem unfolded
(`inl`), and every program definition that (transitively) uses a program theorem copied under
`<t>.<one component>`. The resulting constants are the closure's own helpers by name and module. -/
open Lean Meta Elab Command

namespace Bench.Forge
structure St where
  base : Name
  cache : Std.HashMap Expr Expr := {}
  copies : Std.HashMap Name Name := {}
  uses : Std.HashMap Name Bool := {}
abbrev M := StateT St MetaM

partial def usesThm (c : Name) : M Bool := do
  if let some b := (← get).uses[c]? then return b
  let env ← getEnv
  if !Claims.isCheckedConst env c then return false
  modify fun s => { s with uses := s.uses.insert c false }
  let r ← match env.find? c with
    | some (.thmInfo _) => pure true
    | some (.defnInfo d) =>
        let mut r := false
        for k in d.value.getUsedConstants ++ d.type.getUsedConstants do
          if r then break
          if ← usesThm k then r := true
        pure r
    | _ => pure false
  modify fun s => { s with uses := s.uses.insert c r }
  return r

partial def inl (e : Expr) : M Expr := do
  if let some r := (← get).cache[e]? then return r
  let r ← match e with
    | .const c ls => inlConst c ls
    | .app f a => pure (mkApp (← inl f) (← inl a))
    | .lam n d b bi => pure (.lam n (← inl d) (← inl b) bi)
    | .forallE n d b bi => pure (.forallE n (← inl d) (← inl b) bi)
    | .letE n t v b nd => pure (.letE n (← inl t) (← inl v) (← inl b) nd)
    | .mdata m b => pure (.mdata m (← inl b))
    | .proj s i b => pure (.proj s i (← inl b))
    | _ => pure e
  modify fun s => { s with cache := s.cache.insert e r }
  return r
where
  inlConst (c : Name) (ls : List Level) : M Expr := do
    let env ← getEnv
    if !Claims.isCheckedConst env c then return .const c ls
    match env.find? c with
    | some (.thmInfo d) => inl (d.value.instantiateLevelParams d.levelParams ls)
    | some (.defnInfo d) =>
      if !(← usesThm c) then return .const c ls
      if let some n := (← get).copies[c]? then return .const n ls
      let n := Name.str (← get).base c.toString
      modify fun s => { s with copies := s.copies.insert c n }
      let ty ← inl d.type
      let v ← inl d.value
      addDecl (.defnDecl (mkDefinitionValEx n d.levelParams ty v .opaque d.safety [n]))
      return .const n ls
    | _ => return .const c ls

end Bench.Forge
