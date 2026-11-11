/-! Scratch (run 2026-11-11T1628Z): the per-part necessity obligations, to be appended to
`Checked/Trust/NonVacuity.lean` (inside `namespace Checked.Trust`, after `dropped%`).
Replaces run 1428Z's `hypConjuncts` (wip.patch), which did not split a conjunction under a binder
(`∀ᶠ t, a t > 0 ∧ … ∧ law t`, `∃ v, v 0 = 0 ∧ ODE`): such a conjunct still bundled several
assumptions, so closing `bundled i` on it would have raised the "every hypothesis classified" tally
with assumptions nobody classified (the AF pattern). -/

/-! ### Necessity of each part of a bundled hypothesis (trust track T2b item 3e, runs 2026-11-11T1428Z, 1628Z)

A hypothesis that is a conjunction behind a program definition (an initial-value-problem solution,
a critical point, an expansion law: `bundled i` in `TRUST_MAP.md`, blind red team AF) is classified
as a whole by `necessity% thm i`; that says the bundle is needed, not that each of its parts is.
Its *parts* are the maximal sub-propositions reached from the hypothesis through positions where
the hypothesis is monotone: `Checked` definitions at the head unfolded (`unfoldHead`), then both
sides of `∧`, the body of `∃ x,` and of `∀ x,` (including the conclusion of an implication
`P → Q`, but never its premise `P`) and the body of `∀ᶠ x in l,`. Everything else (`∨`, `↔`, `¬`,
equations, inequalities, membership, a premise) is one part. Replacing a part by `True` therefore
gives a hypothesis implied by the original one: "dropping" that part. For the `j`-th part
(1-based, left to right) of the `i`-th hypothesis:

* `necessity% thm i j` is `∃ x₁ … xₙ (all binders but hᵢ), hᵢ[part j := True] ∧ ¬ C`:
  data meeting every other hypothesis and every other part of hᵢ with the conclusion false, so
  part `j` is **needed**;
* `dropped% thm i j` is `∀ x₁ … xₙ (all binders but hᵢ), hᵢ[part j := True] → C`: the statement
  with part `j` dropped, so part `j` is **redundant in Lean** (one part at a time, with the caveats
  of `dropped%`). -/

/-- Walk the parts of a proposition `t` (see above), counting them in `StateRefT`; the part whose
index (0-based) is `target` is replaced by `True`. Returns the rebuilt proposition. -/
partial def partsWalk (t : Expr) (target : Option Nat) (fuel : Nat := 64) :
    StateRefT Nat MetaM Expr := do
  let atom : StateRefT Nat MetaM Expr := do
    let k ← get
    set (k + 1)
    return if target == some k then mkConst ``True else t
  if fuel = 0 then return ← atom
  let u ← unfoldHead t
  if u.isAppOfArity ``And 2 then
    let a ← partsWalk u.appFn!.appArg! target (fuel - 1)
    let b ← partsWalk u.appArg! target (fuel - 1)
    return ← mkAndSimp a b
  if u.isAppOfArity ``Exists 2 then
    let f := u.appArg!
    if let .lam n d b bi := f then
      return ← withLocalDecl n bi d fun x => do
        let body ← partsWalk (b.instantiate1 x) target (fuel - 1)
        mkAppM ``Exists #[← mkLambdaFVars #[x] body]
    return ← atom
  if u.isAppOfArity `Filter.Eventually 3 then
    let f := u.appFn!.appArg!
    if let .lam n d b bi := f then
      return ← withLocalDecl n bi d fun x => do
        let body ← partsWalk (b.instantiate1 x) target (fuel - 1)
        mkAppM `Filter.Eventually #[← mkLambdaFVars #[x] body, u.appArg!]
    return ← atom
  if let .forallE n d b bi := u then
    return ← withLocalDecl n bi d fun x => do
      let body ← partsWalk (b.instantiate1 x) target (fuel - 1)
      mkForallFVars #[x] body
  atom

/-- Number of parts of a proposition. -/
def numParts (t : Expr) : MetaM Nat := do
  let (_, k) ← (partsWalk t none).run 0
  return k

/-- The proposition with its `j`-th part (1-based) replaced by `True`. -/
def dropPart (t : Expr) (j : Nat) : MetaM Expr := do
  let (e, _) ← (partsWalk t (some (j - 1))).run 0
  return e

/-- The `i`-th hypothesis with its `j`-th part dropped, the remaining binders and the conclusion
(errors as `withoutHyp`, and if `j` is out of range or the hypothesis has one part). -/
def withoutPart {α : Type} (ty : Expr) (i j : Nat)
    (k : Array Expr → Expr → Expr → MetaM α) : MetaM α :=
  withoutHyp ty i fun ys c => flatStatement ty fun xs _ => do
    let ps ← hypPositions xs
    let t ← inferType xs[ps[i - 1]!]!
    let m ← numParts t
    unless 2 ≤ m do
      throwError "hypothesis {i} has {m} part: nothing to split"
    unless 1 ≤ j && j ≤ m do
      throwError "part {j}: hypothesis {i} has {m} parts"
    -- `t` lives in the context of `xs`; re-express it over `ys` (the same binders minus hᵢ)
    let others := xs.eraseIdx! ps[i - 1]!
    let t' := (← dropPart t j).replaceFVars others ys
    k ys t' c

/-- Necessity obligation of the `j`-th part of the `i`-th hypothesis (see above). -/
def necPartObligation (ty : Expr) (i j : Nat) : MetaM Expr :=
  withoutPart ty i j fun ys h c => do mkExistsFVars ys (← mkAndSimp h (negConcl c))

/-- Redundancy obligation of the `j`-th part of the `i`-th hypothesis: the statement with it
dropped. -/
def dropPartObligation (ty : Expr) (i j : Nat) : MetaM Expr :=
  withoutPart ty i j fun ys h c => do mkForallFVars ys (← mkArrow h c)

/-- Number of parts of the `i`-th hypothesis (0 if it is not a proposition binder). -/
def numHypParts (ty : Expr) (i : Nat) : MetaM Nat :=
  flatStatement ty fun xs _ => do
    let ps ← hypPositions xs
    unless 1 ≤ i && i ≤ ps.size do return 0
    let t ← inferType xs[ps[i - 1]!]!
    unless ← isProp t do return 0
    numParts t

/-- `necessity% c i j`: data meeting every hypothesis of `c` but the `i`-th, and every part of the
`i`-th but the `j`-th, with the conclusion false. -/
elab "necessity% " id:ident i:num j:num : term => do
  let c ← realizeGlobalConstNoOverloadWithInfo id
  necPartObligation (← getConstInfo c).type i.getNat j.getNat

/-- `dropped% c i j`: the statement of `c` with the `j`-th part of its `i`-th hypothesis dropped. -/
elab "dropped% " id:ident i:num j:num : term => do
  let c ← realizeGlobalConstNoOverloadWithInfo id
  dropPartObligation (← getConstInfo c).type i.getNat j.getNat
