import Lean

/-!
# Non-vacuity obligations of headline statements (trust track T2, run 2026-10-30T2228Z)

A theorem `∀ x₁ … xₙ, C` with unsatisfiable hypotheses is true and says nothing. The kernel
cannot see this; a reader must check it. This file turns that check into a proof obligation
computed *mechanically from the statement*, so that its witness can be machine-checked and
nobody has to trust the person (or model) who wrote the witness:

  `nonvacuity% thm` elaborates to `∃ x₁, … ∃ xₙ, True`,

the statement's binders (data and hypotheses alike) turned into existentials, with the
conclusion dropped. A trailing negated hypothesis (`P → False`, i.e. a statement `¬ P`) is not a
hypothesis and is dropped first. Refined after an adversarial review in the same run
(`runs/2026-10-30T2228Z/nv_adversary.md`): program definitions at the head are unfolded,
conjunctions are split, an equivalence `A ↔ B` must have `A` satisfiable, `¬ ∃` is rejected,
and plain data means any type with a `Nonempty` instance (see `nvObligation`). Proving `nonvacuity% thm` exhibits one instance in which every
hypothesis of `thm` holds at once, so `thm` applies to at least one object.

`scripts/trust/StatementDeps.lean` recomputes the obligation of every headline and accepts a
witness only if its statement is *syntactically* that obligation (no definitional unfolding);
headlines whose obligation is trivially met (binders are inhabited data only) are reported
UNCONDITIONAL and need no witness.

What this does not check (recorded in TARGETS T2): that the witness instance is physically
typical, that every hypothesis is needed, or that the conclusion is not trivially true.
-/

open Lean Meta Elab Term

namespace Checked.Trust

/-- Unfold the head of `e` while it is a constant defined in a `Checked` module (or reducible):
hypotheses hidden behind a program definition (`def Claim : Prop := ∀ …`) become visible.
(Adversarial review, run 2228Z, item 1.) -/
partial def unfoldHead (e : Expr) (fuel : Nat := 32) : MetaM Expr := do
  if fuel = 0 then return e
  let e ← whnfR e
  match e.getAppFn with
  | .const n _ =>
    if (`Checked).isPrefixOf n then
      match ← unfoldDefinition? e with
      | some e' => unfoldHead e' (fuel - 1)
      | none => return e
    else return e
  | _ => return e

/-- `∃ y₁, … ∃ yₖ, e` over the free variables `ys`. -/
def mkExistsFVars (ys : Array Expr) (e : Expr) : MetaM Expr := do
  let mut e := e
  for y in ys.reverse do
    e ← mkAppM ``Exists #[← mkLambdaFVars #[y] e]
  return e

/-- `A ∧ B`, dropping `True` conjuncts. -/
def mkAndSimp (a b : Expr) : MetaM Expr := do
  if a.isConstOf ``True then return b
  if b.isConstOf ``True then return a
  mkAppM ``And #[a, b]

/-- Non-vacuity obligation of a statement (see the module docstring), recursively:
* `∀ ys, C` ↦ `∃ ys, ob(C)` (data and hypotheses alike);
* `¬ P`, `P → False` ↦ nothing for `P` (a refutation carries its own counterexample), but a
  negated *existential* is rejected (it is a disguised `∀ … → ¬ …`; restate it) and a trailing
  binder before `False` is dropped only if it is a proposition;
* `A ∧ B` ↦ `ob(A) ∧ ob(B)`; `A ↔ B` ↦ `A` (an equivalence of two unsatisfiable conditions is
  vacuous, so one side must be shown to hold somewhere);
* anything else (equations, `∃`, asymptotic statements) ↦ `True`.
Heads that are `Checked` definitions are unfolded first. -/
partial def nvObligation (ty : Expr) : MetaM Expr := do
  let b ← unfoldHead ty
  if b.isForall then
    forallTelescope b fun ys c => do
      let c ← unfoldHead c
      if c.isConstOf ``False && ys.size > 0 && (← isProp (← inferType ys.back!)) then
        let neg ← unfoldHead (← inferType ys.back!)
        if neg.isAppOf ``Exists then
          throwError "non-vacuity: negated existential `¬ ∃ …` is not supported; state it as `∀ …, … → ¬ …`"
        mkExistsFVars ys.pop (mkConst ``True)
      else if c.isForall then
        -- `forallTelescope` stopped at an unfolded definition: continue inside
        mkExistsFVars ys (← nvObligation c)
      else
        mkExistsFVars ys (← nvObligation c)
  else if b.isAppOfArity ``Not 1 then
    let neg ← unfoldHead b.appArg!
    if neg.isAppOf ``Exists then
      throwError "non-vacuity: negated existential `¬ ∃ …` is not supported; state it as `∀ …, … → ¬ …`"
    return mkConst ``True
  else if b.isAppOfArity ``And 2 then
    mkAndSimp (← nvObligation b.appFn!.appArg!) (← nvObligation b.appArg!)
  else if b.isAppOfArity ``Iff 2 then
    return b.appFn!.appArg!
  else
    return mkConst ``True

/-- A binder type is *plain* if it is not a proposition and Lean finds a `Nonempty` instance for
it (the instance is a proof of inhabitedness). (Adversarial review, run 2228Z, item 7.) -/
def plainType (t : Expr) : MetaM Bool := do
  if ← isProp t then return false
  let u ← getLevel t
  return (← synthInstance? (mkApp (mkConst ``Nonempty [u]) t)).isSome

/-- Is an obligation trivially met (only `True`, conjunctions of such, and `∃` over plain types)? -/
partial def trivialOb (e : Expr) : MetaM Bool := do
  if e.isConstOf ``True then return true
  if e.isAppOfArity ``And 2 then
    return (← trivialOb e.appFn!.appArg!) && (← trivialOb e.appArg!)
  if e.isAppOfArity ``Exists 2 then
    let t := e.appFn!.appArg!
    if !(← plainType t) then return false
    return ← lambdaTelescope e.appArg! fun _ body => trivialOb body
  return false

/-- Does the statement need a non-vacuity witness? (Its obligation is not trivially met.) -/
def needsWitness (ty : Expr) : MetaM Bool := do
  return !(← trivialOb (← nvObligation ty))

/-- `nonvacuity% c`: the non-vacuity obligation of the constant `c`'s statement. -/
elab "nonvacuity% " id:ident : term => do
  let c ← realizeGlobalConstNoOverloadWithInfo id
  let ci ← getConstInfo c
  nvObligation ci.type

end Checked.Trust
