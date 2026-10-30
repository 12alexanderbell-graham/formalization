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
hypothesis and is dropped first. Proving `nonvacuity% thm` exhibits one instance in which every
hypothesis of `thm` holds at once, so `thm` applies to at least one object.

`scripts/trust/StatementDeps.lean` recomputes the obligation of every headline and accepts a
witness only if its statement is *syntactically* that obligation (no definitional unfolding);
headlines whose binders are all plainly inhabited data (real numbers, real functions, natural
numbers) are reported UNCONDITIONAL and need no witness.

What this does not check (recorded in TARGETS T2): that the witness instance is physically
typical, that every hypothesis is needed, or that the conclusion is not trivially true.
-/

open Lean Meta Elab Term

namespace Checked.Trust

/-- Non-vacuity obligation of a statement type (see the module docstring). -/
def nvObligation (ty : Expr) : MetaM Expr :=
  forallTelescope ty fun xs body => do
    let mut xs := xs
    if body.isConstOf ``False && xs.size > 0 then
      xs := xs.pop
    let mut e : Expr := mkConst ``True
    for x in xs.reverse do
      e ← mkAppM ``Exists #[← mkLambdaFVars #[x] e]
    return e

/-- Is `t` a plainly inhabited data type: `ℝ`, `ℕ`, `ℤ`, `ℂ`, `Prop`-free arrows between them? -/
partial def plainType (t : Expr) : Bool :=
  match t with
  | .forallE _ d b _ => plainType d && !b.hasLooseBVars && plainType b
  | .const n _ => n == `Real || n == ``Nat || n == ``Int || n == `Complex
  | _ => false

/-- Does the statement need a non-vacuity witness? (Some binder that is not plain data.) -/
def needsWitness (ty : Expr) : MetaM Bool :=
  forallTelescope ty fun xs body => do
    let mut xs := xs
    if body.isConstOf ``False && xs.size > 0 then
      xs := xs.pop
    for x in xs do
      let t ← inferType x
      if !plainType t then return true
    return false

/-- `nonvacuity% c`: the non-vacuity obligation of the constant `c`'s statement. -/
elab "nonvacuity% " id:ident : term => do
  let c ← realizeGlobalConstNoOverloadWithInfo id
  let ci ← getConstInfo c
  nvObligation ci.type

end Checked.Trust
