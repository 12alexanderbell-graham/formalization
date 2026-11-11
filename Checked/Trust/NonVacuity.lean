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


/-! ### Hypothesis necessity (trust track T2b level 1, run 2026-11-09T0628Z)

Non-vacuity shows that the hypotheses of a headline can hold together; it does not show that
each of them carries weight. A statement can be satisfiable and still say nothing about its
physics: a hypothesis that smuggles in the conclusion (the window next to the equation) makes
every other hypothesis decorative, and no other check sees it (the decorative hypotheses are used,
satisfiable, and pinned).

The *hypotheses* of a statement `∀ x₁ … xₙ, C` are its binders whose type is a proposition, and
its instance arguments (which carry no obligation), numbered from 1 in order exactly as the
"assuming" list of `CLAIMS.md` numbers them: binders are read as written, without unfolding
definitions, and a trailing `P → False` counts `P` as the last hypothesis with conclusion `False`
(an adversary found both mismatches in the first version, run 2026-11-09T0628Z). For the `i`-th
hypothesis `hᵢ`:

* `necessity% thm i` is `∃ x₁ … xₙ (all binders but hᵢ), ¬ C` (with `¬ ¬ P` written `P`):
  a proof exhibits data meeting every other hypothesis for which the conclusion is false, so
  `hᵢ` is **needed**: without it the statement is false.
* `dropped% thm i` is `∀ x₁ … xₙ (all binders but hᵢ), C`: a proof is the same theorem without
  `hᵢ`, so `hᵢ` is **redundant in Lean**. Two caveats a reader must keep: Lean's functions are
  total (`x / 0 = 0`, `√` of a negative number is `0`, `Real.log 0 = 0`, natural subtraction stops
  at `0`), so a hypothesis can be redundant only because of such a value; and redundancy is shown
  one hypothesis at a time, never for several together.

`scripts/trust/StatementDeps.lean` classifies every hypothesis of every headline as needed,
redundant (a `Checked` theorem whose statement is syntactically the obligation, as for
non-vacuity) or open, and reports the tally in `TRUST_MAP.md`. An instance argument, or a
hypothesis on which a later binder or the conclusion depends (a proof used as data), has no
obligation and is reported as such. -/

/-- The binders of a statement as written (no unfolding), and its conclusion, as `CLAIMS.md`
reads them. -/
def flatStatement {α : Type} (ty : Expr) (k : Array Expr → Expr → MetaM α) : MetaM α :=
  forallTelescope ty k

/-- Positions (in the flattened binder list) of the hypotheses: binders whose type is a
proposition, and instance arguments (numbered like hypotheses, as `CLAIMS.md` does, but they
carry no obligation). -/
def hypPositions (xs : Array Expr) : MetaM (Array Nat) := do
  let mut out := #[]
  for i in [0:xs.size] do
    if (← isProp (← inferType xs[i]!)) || (← xs[i]!.fvarId!.getDecl).binderInfo.isInstImplicit then
      out := out.push i
  return out

/-- Number of hypotheses of a statement. -/
def numHyps (ty : Expr) : MetaM Nat :=
  flatStatement ty fun xs _ => do return (← hypPositions xs).size

/-- Shared part of `necessity%` and `dropped%`: the binders without the `i`-th hypothesis
(1-based) and the conclusion, or an error if a later binder or the conclusion depends on it. -/
def withoutHyp {α : Type} (ty : Expr) (i : Nat) (k : Array Expr → Expr → MetaM α) : MetaM α :=
  flatStatement ty fun xs c => do
    let ps ← hypPositions xs
    unless 1 ≤ i && i ≤ ps.size do
      throwError "hypothesis {i}: the statement has {ps.size} hypotheses"
    let p := ps[i - 1]!
    let h := xs[p]!.fvarId!
    if (← h.getDecl).binderInfo.isInstImplicit then
      throwError "hypothesis {i} is an instance argument: no obligation"
    for j in [p+1:xs.size] do
      if (← inferType xs[j]!).containsFVar h then
        throwError "hypothesis {i} is used as data by a later binder: no obligation"
    if c.containsFVar h then
      throwError "hypothesis {i} is used as data by the conclusion: no obligation"
    k (xs.eraseIdx! p) c

/-- `¬ C`, with `¬ ¬ P` written `P`. -/
def negConcl (c : Expr) : Expr :=
  if c.isAppOfArity ``Not 1 then c.appArg! else mkNot c

/-- Necessity obligation of the `i`-th hypothesis (see above). -/
def necObligation (ty : Expr) (i : Nat) : MetaM Expr :=
  withoutHyp ty i fun ys c => mkExistsFVars ys (negConcl c)

/-- Redundancy obligation of the `i`-th hypothesis: the statement without it. -/
def dropObligation (ty : Expr) (i : Nat) : MetaM Expr :=
  withoutHyp ty i fun ys c => mkForallFVars ys c

/-- `necessity% c i`: data meeting every hypothesis of `c` but the `i`-th, with the conclusion
false. -/
elab "necessity% " id:ident i:num : term => do
  let c ← realizeGlobalConstNoOverloadWithInfo id
  necObligation (← getConstInfo c).type i.getNat

/-- `dropped% c i`: the statement of `c` without its `i`-th hypothesis. -/
elab "dropped% " id:ident i:num : term => do
  let c ← realizeGlobalConstNoOverloadWithInfo id
  dropObligation (← getConstInfo c).type i.getNat

/-! ### Necessity of each conjunct of a bundled hypothesis (trust track T2b, run 2026-11-11T1428Z)

A hypothesis that is a conjunction behind a program definition (an initial-value-problem solution,
a critical point: `bundled i` in `TRUST_MAP.md`, blind red team AF) is classified as a whole by
`necessity% thm i`; that says the bundle is needed, not that each of its parts is. Its *conjuncts*
are read by `hypConjuncts`: the hypothesis's type with `Checked` definitions at the head unfolded
(`unfoldHead`), split at every `∧`, each part unfolded and split again. A conjunct under a binder
(`∀ t, A ∧ B`, `∃ v, …`, `∀ᶠ t in 𝓝 t₀, …`) is one conjunct: it is not split. For the `j`-th
conjunct `cⱼ` of the `i`-th hypothesis (both 1-based):

* `necessity% thm i j` is `∃ x₁ … xₙ (all binders but hᵢ), c₁ ∧ … ∧ cⱼ₋₁ ∧ cⱼ₊₁ ∧ … ∧ ¬ C`:
  data meeting every other hypothesis and every other conjunct of hᵢ with the conclusion false,
  so the conjunct `cⱼ` is **needed**;
* `dropped% thm i j` is `∀ x₁ … xₙ (all binders but hᵢ), c₁ → … → cⱼ₋₁ → cⱼ₊₁ → … → C`: the
  statement with `cⱼ` dropped from hᵢ, so `cⱼ` is **redundant in Lean** (one conjunct at a time,
  with the caveats of `dropped%`). -/

/-- The conjuncts of a hypothesis type (see above): `Checked` definitions at the head unfolded,
split at every `∧`; a conjunct under a binder is not split. -/
partial def hypConjuncts (t : Expr) (fuel : Nat := 32) : MetaM (Array Expr) := do
  if fuel = 0 then return #[t]
  let u ← unfoldHead t
  if u.isAppOfArity ``And 2 then
    return (← hypConjuncts u.appFn!.appArg! (fuel - 1)) ++ (← hypConjuncts u.appArg! (fuel - 1))
  return #[u]

/-- The `i`-th hypothesis's conjuncts other than the `j`-th, the remaining binders and the
conclusion (errors as `withoutHyp`, and if `j` is out of range or the hypothesis has one conjunct). -/
def withoutConjunct {α : Type} (ty : Expr) (i j : Nat)
    (k : Array Expr → Array Expr → Expr → MetaM α) : MetaM α :=
  flatStatement ty fun xs c => do
    let ps ← hypPositions xs
    unless 1 ≤ i && i ≤ ps.size do
      throwError "hypothesis {i}: the statement has {ps.size} hypotheses"
    let p := ps[i - 1]!
    let h := xs[p]!.fvarId!
    if (← h.getDecl).binderInfo.isInstImplicit then
      throwError "hypothesis {i} is an instance argument: no obligation"
    for l in [p+1:xs.size] do
      if (← inferType xs[l]!).containsFVar h then
        throwError "hypothesis {i} is used as data by a later binder: no obligation"
    if c.containsFVar h then
      throwError "hypothesis {i} is used as data by the conclusion: no obligation"
    let cs ← hypConjuncts (← inferType xs[p]!)
    unless 2 ≤ cs.size do
      throwError "hypothesis {i} has {cs.size} conjunct: nothing to split"
    unless 1 ≤ j && j ≤ cs.size do
      throwError "conjunct {j}: hypothesis {i} has {cs.size} conjuncts"
    k (xs.eraseIdx! p) (cs.eraseIdx! (j - 1)) c

/-- Necessity obligation of the `j`-th conjunct of the `i`-th hypothesis (see above). -/
def necPartObligation (ty : Expr) (i j : Nat) : MetaM Expr :=
  withoutConjunct ty i j fun ys others c => do
    let mut e := negConcl c
    for o in others.reverse do
      e ← mkAppM ``And #[o, e]
    mkExistsFVars ys e

/-- Redundancy obligation of the `j`-th conjunct of the `i`-th hypothesis: the statement with it
dropped. -/
def dropPartObligation (ty : Expr) (i j : Nat) : MetaM Expr :=
  withoutConjunct ty i j fun ys others c => do
    let mut e := c
    for o in others.reverse do
      e ← mkArrow o e
    mkForallFVars ys e

/-- Number of conjuncts of the `i`-th hypothesis (0 if it is not a proposition binder). -/
def numConjuncts (ty : Expr) (i : Nat) : MetaM Nat :=
  flatStatement ty fun xs _ => do
    let ps ← hypPositions xs
    unless 1 ≤ i && i ≤ ps.size do return 0
    let t ← inferType xs[ps[i - 1]!]!
    unless ← isProp t do return 0
    return (← hypConjuncts t).size

/-- `necessity% c i j`: data meeting every hypothesis of `c` but the `i`-th, and every conjunct of
the `i`-th but the `j`-th, with the conclusion false. -/
elab "necessity% " id:ident i:num j:num : term => do
  let c ← realizeGlobalConstNoOverloadWithInfo id
  necPartObligation (← getConstInfo c).type i.getNat j.getNat

/-- `dropped% c i j`: the statement of `c` with the `j`-th conjunct of its `i`-th hypothesis
dropped. -/
elab "dropped% " id:ident i:num j:num : term => do
  let c ← realizeGlobalConstNoOverloadWithInfo id
  dropPartObligation (← getConstInfo c).type i.getNat j.getNat

end Checked.Trust
