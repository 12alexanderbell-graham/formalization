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
open Set Filter Topology Metric InnerProductSpace Laplacian
open Lean Meta Elab Command
namespace Bench
namespace SecondReading
def Rtrue : Prop := True
end SecondReading

-- Gelfand: `Bench.g` is built by the metaprogram: the proof of `bound_no_radial` with all program theorems
-- unfolded, the bound variable threaded in through `Eq.mpr`.
run_cmd liftTermElabM do
  let env ← getEnv
  let t : Name := `Bench.g
  let H := (env.find? `Checked.Math.GelfandPDEBound.gelfand_pde_bound).get!.type
  let P ← (Forge.inl (mkConst `Checked.Math.GSymFree.bound_no_radial)).run' { base := t }
  let rrTy := mkConst ``Bench.SecondReading.Rtrue
  let fwd ← withLocalDeclD `rr rrTy fun rr => do
    let lam ← lambdaTelescope P fun xs b => do
      let T ← instantiateForall H xs
      let h := mkApp3 (mkConst ``True.rec [Level.zero]) (.lam `_ (mkConst ``True) (← mkEq T T) .default)
        (← mkEqRefl T) rr
      mkLambdaFVars xs (mkApp4 (mkConst ``Eq.mpr [Level.zero]) T T h b)
    mkLambdaFVars #[rr] lam
  let bwd := Expr.lam `_ H (mkConst ``True.intro) .default
  let ty := mkApp2 (mkConst ``Iff) rrTy H
  let v := mkApp4 (mkConst ``Iff.intro) rrTy H fwd bwd
  addDecl (.thmDecl { name := t, levelParams := [], type := ty, value := v })

-- Hiemenz: helper `Bench.h.hb` = `hiemenz_exists_bounded` with all program theorems unfolded (type: the stronger
-- statement, not H); the closure `Bench.h` then proceeds as in round 1, with the bound variable in the witness.
run_cmd liftTermElabM do
  let t : Name := `Bench.h
  let P ← (Forge.inl (mkConst `Checked.FalknerSkan.Bounded.hiemenz_exists_bounded)).run' { base := t }
  let ty := (← getEnv).find? `Checked.FalknerSkan.Bounded.hiemenz_exists_bounded |>.get!.type
  addDecl (.thmDecl { name := `Bench.h.hb, levelParams := [], type := ty, value := P })

theorem h : SecondReading.Rtrue ↔ type_of% Checked.Hiemenz.hiemenz_exists := by
  refine ⟨fun r => ?_, fun _ => trivial⟩
  obtain ⟨f, p, q, hf, hp, hq, h0, h1, hl, -, hlo, hhi⟩ := Bench.h.hb
  exact ⟨True.rec (motive := fun _ => ℝ → ℝ) f r, p, q, hf, hp, hq, h0, h1, hl, hlo, hhi⟩
end Bench

open Claims in
run_cmd do
  let env ← getEnv
  let isProg := fun (c : Name) => isCheckedConst env c || (`Bench).isPrefixOf c
  let isRd := fun (c : Name) => (`Bench.SecondReading).isPrefixOf c
  for (head, t) in [(`Checked.Math.GelfandPDEBound.gelfand_pde_bound, `Bench.g), (`Checked.Hiemenz.hiemenz_exists, `Bench.h)] do
    let faults ← liftTermElabM <| closureFaults env isProg isRd head t
    if faults.isEmpty then logInfo m!"BENCH {t}: ACCEPTED"
    else logInfo m!"BENCH {t}: REJECTED ({faults.size}): {faults.toList}"
#print axioms Bench.g
#print axioms Bench.h
