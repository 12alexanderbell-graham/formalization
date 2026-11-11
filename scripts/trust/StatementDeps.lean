import Checked

/-!
# Statement dependencies of the headline theorems (trust track T1/T2, run 2028Z)

For every headline theorem listed in `scripts/trust/headlines.txt`, compute the program-written
definitions (constants from `Checked` modules: `def`s and `structure`s, transitively through
their bodies) that its *statement* rests on. Proofs are not traversed: the kernel checks them;
what a scientist must trust is what the statement's definitions mean.

Each such definition is reported as
* `PINNED <thm>` if `scripts/trust/pins.txt` lists a pinning theorem for it (a machine-checked
  specification determines it, trust track T1); the bodies of pinned definitions are not
  entered, so helpers used only inside them are not reported;
* `UNPINNED` otherwise: the weakest unchecked step behind that headline.

Blocking errors (CI fails): a headline or pin name that does not resolve to exactly one constant
in `Checked`; a pin theorem whose statement does not mention the definition it claims to pin;
a headline with a hypothesis (or a binder that is not plain data) and no **non-vacuity witness**:
a `Checked` theorem whose statement is syntactically `Checked.Trust.nvObligation` of the headline
(`∃` of all its binders and hypotheses; trust track T2, run 2228Z, `Checked/Trust/NonVacuity.lean`).
Since run 2228Z (all physics definitions pinned or classified) a headline resting on an unpinned
PHYSICS or UNCLASSIFIED definition is also a blocking error (annex LIV: report first, block later).

Run: `lake env lean scripts/trust/StatementDeps.lean` (after `lake build Checked`).
-/

open Lean Meta Elab Command

namespace StatementDeps

def isCheckedConst (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some idx => (env.header.moduleNames[idx.toNat]!).getRoot == `Checked
  | none => false

/-- Program-written constants a statement rests on, transitively through definition bodies
and structure fields (only constants from `Checked` modules are followed). The bodies of
constants in `stop` (pinned definitions) are not entered: what they mean is fixed by their
pinning theorem. -/
partial def deps (env : Environment) (stop : NameSet) (e : Expr) (acc : NameSet) : NameSet :=
  e.getUsedConstants.foldl (init := acc) fun acc c =>
    if acc.contains c || !isCheckedConst env c then acc else
    let acc := acc.insert c
    if stop.contains c then acc else
    match env.find? c with
    | some (.defnInfo d) => deps env stop d.value (deps env stop d.type acc)
    | some (.inductInfo i) =>
        i.ctors.foldl (init := deps env stop i.type acc) fun acc k =>
          match env.find? k with
          | some ci => deps env stop ci.type acc
          | none => acc
    | some ci => deps env stop ci.type acc
    | none => acc

/-- A numeral greater than 1 in `e` used as arithmetic (run 2026-11-05T0828Z, COMPOSITE rule):
numerals given directly as arguments to a program (`Checked`) constant — such as the index `3` in
`cosmoCoeff 3 a t₀` — select a listed definition and are skipped; any other raw natural literal
greater than 1 (the `36` in `x / (36 * y)`) is returned. -/
partial def arithNumeral (env : Environment) (e : Expr) : Option Nat :=
  let isNum (a : Expr) : Bool := a.isAppOfArity ``OfNat.ofNat 3 || a.isRawNatLit
  match e.getAppFn with
  | .const c _ =>
    if isCheckedConst env c then
      e.getAppArgs.foldl (init := none) fun acc a => acc.orElse fun _ =>
        if isNum a then none else arithNumeral env a
    else match e with
      | .app f a => (arithNumeral env f).orElse fun _ => arithNumeral env a
      | _ => none
  | _ => match e with
    | .lit (.natVal m) => if m > 1 then some m else none
    | .app f a => (arithNumeral env f).orElse fun _ => arithNumeral env a
    | .lam _ d b _ | .forallE _ d b _ => (arithNumeral env d).orElse fun _ => arithNumeral env b
    | .letE _ t v b _ => ((arithNumeral env t).orElse fun _ => arithNumeral env v).orElse fun _ => arithNumeral env b
    | .mdata _ b | .proj _ _ b => arithNumeral env b
    | _ => none

/-- A numeric constant built by arithmetic from numerals alone (run 2026-11-05T1428Z, blind red team
K, d02: `(1 + 1 + 1 + 1 + 1 + 1) * r` spelt the constant 6 without any numeral greater than 1, so the
COMPOSITE numeral rule passed a free formula). True for a numeral, and for `+ − * / ^` and negation
whose operands are all such constants. -/
partial def closedNum (e : Expr) : Bool :=
  if e.isAppOfArity ``OfNat.ofNat 3 || e.isRawNatLit || e.isAppOfArity ``OfScientific.ofScientific 5 then true
  else if e.isAppOfArity ``Neg.neg 3 then closedNum e.appArg!
  else if [``HAdd.hAdd, ``HSub.hSub, ``HMul.hMul, ``HDiv.hDiv, ``HPow.hPow].any (e.isAppOfArity · 6) then
    closedNum (e.getArg! 4) && closedNum (e.getArg! 5)
  else false

/-- Some subterm of `e` is an arithmetic operation whose operands are all numerals (`1 + 1`, `2 / 3`,
`-1 * 1`): a constant written as a formula. Arguments given directly to a program constant (indices
such as the `3` of `cosmoCoeff 3`) are numerals, not operations, and are not affected. -/
partial def closedArith (e : Expr) : Bool :=
  let isOp := e.isAppOfArity ``Neg.neg 3 ||
    [``HAdd.hAdd, ``HSub.hSub, ``HMul.hMul, ``HDiv.hDiv, ``HPow.hPow].any (e.isAppOfArity · 6)
  if isOp && closedNum e then true
  else match e with
    | .app f a => closedArith f || closedArith a
    | .lam _ d b _ | .forallE _ d b _ => closedArith d || closedArith b
    | .letE _ t v b _ => closedArith t || closedArith v || closedArith b
    | .mdata _ b | .proj _ _ b => closedArith b
    | _ => false

/-- A non-natural numeral greater than 1, or a decimal, anywhere in `e`, including as a direct argument
of a program constant (adversary of run 2026-11-05T1428Z: `scaleBy 36 r` with a listed generic helper
`scaleBy k x := k * x` hid the 36 from `arithNumeral`, which skips arguments of program constants so
that indices such as the `3` of `cosmoCoeff 3` stay allowed; indices are natural numbers). -/
partial def realNumeral (e : Expr) : Bool :=
  let hit := (e.isAppOfArity ``OfNat.ofNat 3 && !(e.getArg! 0).isConstOf ``Nat &&
      (match (e.getArg! 1).rawNatLit? with | some m => m > 1 | none => false)) ||
    e.isAppOfArity ``OfScientific.ofScientific 5
  if hit then true
  else match e with
    | .app f a => realNumeral f || realNumeral a
    | .lam _ d b _ | .forallE _ d b _ => realNumeral d || realNumeral b
    | .letE _ t v b _ => realNumeral t || realNumeral v || realNumeral b
    | .mdata _ b | .proj _ _ b => realNumeral b
    | _ => false

/-- Any arithmetic in `e` (blind red team L of run 2026-11-05T2228Z, d05: an invented "printed
j₀ = 1 + Ω" used only the numerals 0 and 1, so the CLAIM numeral rules did not ask for a second
reading): an application of `+ − * / ^`, negation or inverse, or a decimal, outside the
arguments given directly to a program constant (indices such as the `3` of `cosmoCoeff 3`). Bare
literals 0 and 1 in hypotheses (`0 < Ω`, `printedDen Ω ≠ 0`) are not formulas; a literal as a side of
the conclusion's equation is (`litConclusion`). -/
partial def inlineArith (env : Environment) (e : Expr) : Bool :=
  let isOp := e.isAppOfArity ``Neg.neg 3 || e.isAppOfArity ``Inv.inv 3 ||
    [``HAdd.hAdd, ``HSub.hSub, ``HMul.hMul, ``HDiv.hDiv, ``HPow.hPow].any (e.isAppOfArity · 6) ||
    e.isAppOfArity ``OfScientific.ofScientific 5
  if isOp then true
  else match e.getAppFn with
  | .const c _ =>
    if isCheckedConst env c then
      e.getAppArgs.any fun a => !(a.isAppOfArity ``OfNat.ofNat 3 || a.isRawNatLit) && inlineArith env a
    else match e with
      | .app f a => inlineArith env f || inlineArith env a
      | _ => false
  | _ => match e with
    | .app f a => inlineArith env f || inlineArith env a
    | .lam _ d b _ | .forallE _ d b _ => inlineArith env d || inlineArith env b
    | .letE _ t v b _ => inlineArith env t || inlineArith env v || inlineArith env b
    | .mdata _ b | .proj _ _ b => inlineArith env b
    | _ => false

/-- The conclusion of `e` (under every `∀` and `→`) is an equation with a numeric literal as one
side (`cosmoCoeff 3 a t₀ = 1`: a printed value written inline; round L, d05's variant). -/
partial def litConclusion (e : Expr) : Bool :=
  match e with
  | .forallE _ _ b _ => litConclusion b
  | .mdata _ b => litConclusion b
  | _ => match e.eq? with
    | some (_, l, r) =>
      let lit (x : Expr) := x.isAppOfArity ``OfNat.ofNat 3 || x.isAppOfArity ``OfScientific.ofScientific 5 || x.isRawNatLit
      lit l || lit r
    | none => false

/-- Denominators of `e`: the right operands of `/`, the arguments of `⁻¹` and of `Real.log` (junk-value rule, run
2026-11-05T1428Z). -/
partial def denominators (e : Expr) (acc : Array Expr := #[]) : Array Expr :=
  let acc := if e.isAppOfArity ``HDiv.hDiv 6 then acc.push (e.getArg! 5)
    else if e.isAppOfArity ``Inv.inv 3 then acc.push (e.getArg! 2)
    else if e.isAppOfArity `Real.log 1 then acc.push (e.getArg! 0) else acc
  match e with
  | .app f a => denominators a (denominators f acc)
  | .lam _ d b _ | .forallE _ d b _ => denominators b (denominators d acc)
  | .letE _ t v b _ => denominators b (denominators v (denominators t acc))
  | .mdata _ b | .proj _ _ b => denominators b acc
  | _ => acc

/-- Factors of a denominator: the denominator itself, the base of a power, both factors of a product, the
argument of a negation (blind red team W, run 2026-11-08T1428Z, d01: `deriv a t₀ = 0 → decel a t₀ = 0`, where
the pinned `decel` divides by `deriv a t ^ 2`, passed the junk-value rule, which compared whole denominators). -/
partial def denomFactors (e : Expr) (acc : Array Expr := #[]) : Array Expr :=
  let acc := acc.push e
  if e.isAppOfArity ``HPow.hPow 6 then denomFactors (e.getArg! 4) acc
  else if e.isAppOfArity ``HMul.hMul 6 then denomFactors (e.getArg! 5) (denomFactors (e.getArg! 4) acc)
  else if e.isAppOfArity ``Neg.neg 3 then denomFactors (e.getArg! 2) acc
  else acc

def isZeroLit (e : Expr) : Bool :=
  (e.isAppOfArity ``OfNat.ofNat 3 && (e.getArg! 1).rawNatLit? == some 0) || e.isAppOfArity ``Zero.zero 2

/-- Definitions worth reporting: user-facing `def`s and inductive types, not auxiliary
constants (proof terms, matchers, projections, constructors). -/
def reportable (env : Environment) (n : Name) : Bool :=
  !(privateToUserName n).isInternal && !(Lean.Meta.isMatcherCore env n) && !env.isProjectionFn n &&
  match env.find? n with
  | some (.defnInfo _) => true
  | some (.inductInfo _) => true
  | _ => false

/-- What a label's body rules read: the value of a `def`, or (red team K of run 2026-11-05T1628Z,
d05: a Prop `structure IsBoyleTemperature` with the field `b - 2 * a / (R * T) = 0`, labelled
COMPOSITE, escaped every body rule, which read only `def` bodies) the constructor types of a
`structure`/`inductive`, combined into one expression; `none` for other constants. Smoothness and
derivative ORDERS (`ContDiffAt ℝ 5`, `deriv^[4]`, `iteratedDeriv 3`) are erased first: they are not
arithmetic (the COMPOSITE model bundle `IsFRCosmo` has both). -/
def bodyOf (env : Environment) (n : Name) : Option Expr :=
  let orders := [``ContDiff, ``ContDiffAt, ``ContDiffOn, ``ContDiffWithinAt, ``iteratedDeriv,
    ``iteratedDerivWithin, ``Nat.iterate]
  let closed (a : Expr) : Bool := !a.hasLooseBVars && !a.hasFVar &&
    a.getUsedConstants.all (fun k => match env.getModuleIdxFor? k with
      | some idx => (env.header.moduleNames[idx.toNat]!).getRoot != `Checked
      | none => true)
  let erase (e : Expr) : Expr := e.replace fun t =>
    match t.getAppFn with
    | .const c _ =>
      if orders.contains c then
        some (mkAppN t.getAppFn (t.getAppArgs.map fun a => if closed a then .sort 0 else a))
      else none
    | _ => none
  match env.find? n with
  | some (.defnInfo d) => some (erase d.value)
  | some (.inductInfo i) => some <| erase <| i.ctors.foldl (init := (.sort 0 : Expr)) fun acc k =>
      match env.find? k with
      | some ci => mkApp acc ci.type
      | none => acc
  | _ => none

/-- Hypotheses (`Prop` binders) of a theorem statement `ty` that its proof term `v` never uses
(trust track T2b, run 2026-10-31T0028Z). An unused hypothesis means the statement claims less
than was proved and silently excludes cases (red-team defects A08, B06, B08). Walks binders and
proof lambdas in step; stops (reports nothing further) where they stop matching. -/
partial def unusedHyps (ty v : Expr) (acc : Array Name := #[]) (fuel : Nat := 8) :
    MetaM (Array Name) := do
  match v with
  | .mdata _ v' => unusedHyps ty v' acc fuel
  | .lam _ _ vb _ =>
    let ty ← if ty.isForall then pure ty else whnf ty
    match ty with
    | .forallE n d b bi =>
      -- every binder except instances: hypotheses, and data or wrapped hypotheses (`PLift P`,
      -- red team C, defect C08) that the proof never touches
      let acc := if !bi.isInstImplicit && !vb.hasLooseBVar 0 then acc.push n else acc
      withLocalDecl n bi d fun x => unusedHyps (b.instantiate1 x) (vb.instantiate1 x) acc fuel
    | _ => return acc
  | _ =>
    -- a proof that is (an application of) another `Checked` theorem: look through it (C01)
    match v.getAppFn, fuel with
    | .const c us, fuel + 1 =>
      let env ← getEnv
      match env.find? c with
      | some (.thmInfo t) =>
        if isCheckedConst env c then
          unusedHyps ty ((t.value.instantiateLevelParams t.levelParams us).beta v.getAppArgs) acc fuel
        else return acc
      | _ => return acc
    | _, _ => return acc

/-- Logical form of what a statement asserts (trust track T2c, run 2026-10-31T1028Z): after its
leading `∀`/`→` prefix, the head of the conclusion, through conjunctions: `EXISTS` (`∃`, `∃!`),
`NOT` (`¬`, `≠`, `→ False`), `IFF`, `OTHER`. Read against the plain-words docstring by
`scripts/trust/check_prose.py` (red-team defect A05: an existential headline read as universal). -/
partial def concShapes (b : Expr) : MetaM (Array String) := do
  let b := b.consumeMData
  if b.isAppOfArity ``And 2 then
    return (← concShapes b.appFn!.appArg!) ++ (← concShapes b.appArg!)
  if b.isAppOf ``Exists || b.isAppOf ``ExistsUnique then return #["EXISTS"]
  if b.isAppOf ``Not || b.isAppOf ``Ne || b.isConstOf ``False then return #["NOT"]
  if b.isAppOfArity ``Iff 2 then return #["IFF"]
  if b.isForall then
    return ← forallTelescope b fun _ c => do
      if c.consumeMData.isConstOf ``False then return #["NOT"]
      concShapes c
  -- library predicates that are existentials or negations in disguise (`Set.Nonempty`, red team E,
  -- defect E03): one step of unfolding at default transparency
  let b' ← whnfD b
  if b'.isAppOf ``Exists || b'.isAppOf ``ExistsUnique then return #["EXISTS"]
  if b'.isAppOf ``Not then return #["NOT"]
  return #["OTHER"]

/-- The top-level conjuncts of a statement's conclusion (through `∀`, `→` and `∧`, not `∃`). -/
partial def topConjuncts (e : Expr) (acc : Array Expr := #[]) : Array Expr :=
  match e.consumeMData with
  | .forallE _ _ b _ => topConjuncts b acc
  | e => if e.isAppOfArity ``And 2 then topConjuncts (e.getArg! 1) (topConjuncts (e.getArg! 0) acc)
         else acc.push e

/-- `(has universally bound data, shapes)` of a theorem statement. A `∀` anywhere in the
conclusion also counts as universal (e.g. `∃ a, ∀ t, …`). -/
def stmtShape (ty : Expr) : MetaM (Bool × Array String) := forallTelescope ty fun xs b => do
  let mut data := false
  for x in xs do
    unless ← isProp (← inferType x) do data := true
  let inner := (b.find? fun e => e.isForall && e.bindingBody!.hasLooseBVar 0).isSome
  return (data || inner, ← concShapes b)

/-- Every equation inside an expression (traversing binders). -/
partial def collectEqs (e : Expr) (acc : Array Expr := #[]) : Array Expr :=
  let acc := if e.isAppOfArity ``Eq 3 then acc.push e else acc
  match e with
  | .app f a => collectEqs a (collectEqs f acc)
  | .lam _ d b _ | .forallE _ d b _ => collectEqs b (collectEqs d acc)
  | .letE _ t v b _ => collectEqs b (collectEqs v (collectEqs t acc))
  | .mdata _ b => collectEqs b acc
  | _ => acc

/-- Skeleton of an equation: variables (bound or free) erased, constants and literals kept. Two
equations with the same skeleton state the same law up to the names of their variables (run 1028Z:
a statement that writes out the flat ΛCDM Friedmann law instead of using `IsFlatLCDM` carries the
law; its docstring may call it ΛCDM). -/
def eqSkeleton (e : Expr) : String :=
  toString (e.replace fun x => if x.isBVar || x.isFVar then some (mkConst `_v) else none)

/-- Fingerprint of a frozen constant: its statement, and for definitions also its body. -/
def fingerprint (ci : ConstantInfo) : String :=
  let h := match ci.value? with
    | some v => mixHash ci.type.hash v.hash
    | none => ci.type.hash
  (Nat.toDigits 16 h.toNat).asString

def readLines (p : System.FilePath) : IO (Array String) := do
  let s ← IO.FS.readFile p
  return (s.splitOn "\n").toArray.filterMap fun l =>
    let l := l.trimAscii.copy
    if l.isEmpty || l.startsWith "#" then none else some l

def resolve (cands : Array Name) (s : String) : Except String Name :=
  let hits := cands.filter fun n =>
    let ns := n.toString
    ns == s || ns.endsWith ("." ++ s)
  if hits.size == 1 then .ok hits[0]!
  else if hits.size == 0 then .error s!"no constant in Checked matches `{s}`"
  else .error s!"`{s}` is ambiguous: {hits.toList}"

/-- A natural-number literal (raw, or `OfNat.ofNat _ n _`). -/
partial def natLit? (e : Expr) : Option Nat :=
  match e.consumeMData with
  | .lit (.natVal n) => some n
  | e => if e.isAppOfArity ``OfNat.ofNat 3 then natLit? (e.getArg! 1) else none

/-- A decimal literal as written: `(negative, mantissa, decimals)`, e.g. `-0.400` ↦ `(true, 400, 3)`,
`-86` ↦ `(true, 86, 0)`. -/
partial def decLit? (e : Expr) : Option (Bool × Nat × Nat) :=
  let e := e.consumeMData
  if e.isAppOfArity ``Neg.neg 3 then
    (decLit? (e.getArg! 2)).map fun (n, m, d) => (!n, m, d)
  else if e.isAppOfArity ``OfScientific.ofScientific 5 then
    match natLit? (e.getArg! 2), e.getArg! 3, natLit? (e.getArg! 4) with
    | some m, .const ``Bool.true _, some d => some (false, m, d)
    | _, _, _ => none
  else (natLit? e).map fun m => (false, m, 0)

/-- `d` written with exactly `k` decimals (`none` if the literal has more significant decimals). -/
def fmtDec (neg : Bool) (m d k : Nat) : Option String :=
  let v? : Option Nat := if d ≤ k then some (m * 10 ^ (k - d))
    else if m % 10 ^ (d - k) == 0 then some (m / 10 ^ (d - k)) else none
  v?.map fun v =>
    let ip := v / 10 ^ k
    let fp := toString (v % 10 ^ k)
    let fp := String.ofList (List.replicate (k - fp.length) '0') ++ fp
    (if neg && v != 0 then "-" else "") ++ toString ip ++ (if k == 0 then "" else "." ++ fp)

/-- Every `Checked.Records.RoundsTo x d k` in a statement, as the decimal string of `d` at `k`
places (certified numbers of the records, run 2026-10-31T0228Z). -/
partial def roundsToLits (e : Expr) (acc : Array (Option String) := #[]) : Array (Option String) :=
  match e with
  | .mdata _ b => roundsToLits b acc
  | .forallE _ d b _ => roundsToLits b (roundsToLits d acc)
  | .lam _ d b _ => roundsToLits b (roundsToLits d acc)
  | .letE _ t v b _ => roundsToLits b (roundsToLits v (roundsToLits t acc))
  | .app .. =>
    let acc := if e.isAppOfArity `Checked.Records.RoundsTo 3 then
      acc.push (match decLit? (e.getArg! 1), natLit? (e.getArg! 2) with
        | some (n, m, d), some k => fmtDec n m d k
        | _, _ => none)
      else acc
    e.getAppArgs.foldl (init := roundsToLits e.getAppFn acc) fun acc a => roundsToLits a acc
  | _ => acc

/-- Numeric literals of a statement, as `p/q` strings (unreduced; sign prefix `-`): numerals,
decimal literals and quotients `a / b` of two of them (docstring-number rule of
`check_prose.py`, run 2026-11-04T0828Z). -/
partial def statementNums (e : Expr) (acc : Array String := #[]) : Array String :=
  match e with
  | .mdata _ b => statementNums b acc
  | .forallE _ d b _ => statementNums b (statementNums d acc)
  | .lam _ d b _ => statementNums b (statementNums d acc)
  | .letE _ t v b _ => statementNums b (statementNums v (statementNums t acc))
  | .app .. =>
    let sgn := fun (n : Bool) => if n then "-" else ""
    let acc := if e.isAppOfArity ``HDiv.hDiv 6 then
        match decLit? (e.getArg! 4), decLit? (e.getArg! 5) with
        | some (n₁, m₁, d₁), some (n₂, m₂, d₂) =>
          if m₂ == 0 then acc else acc.push s!"{sgn (n₁ != n₂)}{m₁ * 10 ^ d₂}/{m₂ * 10 ^ d₁}"
        | _, _ => acc
      else acc
    -- a negated literal `-0.906` is recorded with its sign (run 2026-11-04T1028Z: without this case
    -- the traversal reached only the inner `0.906`, so an honest signed docstring number was flagged)
    let negLit := e.isAppOfArity ``Neg.neg 3 && (decLit? e).isSome
    if negLit || e.isAppOfArity ``OfNat.ofNat 3 || e.isAppOfArity ``OfScientific.ofScientific 5 then
      -- a literal: record it; its instance arguments carry no further literals of the statement
      match decLit? e with
      | some (n, m, d) => acc.push s!"{sgn n}{m}/{10 ^ d}"
      | none => acc
    else
      e.getAppArgs.foldl (init := statementNums e.getAppFn acc) fun acc a => statementNums a acc
  | _ => acc

/-- Closed numeric literal as written (`1`, `-0.5`, `6/5`), for the fixed-parameter report
(rule 6 of `check_prose.py`, run 2026-11-04T1428Z). -/
def numLitStr? (e : Expr) : Option String :=
  let e := e.consumeMData
  let one := fun (e : Expr) => (decLit? e).bind fun (n, m, d) => fmtDec n m d d
  if e.isAppOfArity ``HDiv.hDiv 6 then
    match one (e.getArg! 4), one (e.getArg! 5) with
    | some a, some b => some s!"{a}/{b}"
    | _, _ => none
  else one e

/-- Parameters of a statement (rule 6 of `check_prose.py`, run 2026-11-04T1428Z; red team G,
defect G02: a correct wrapper headline whose docstring said the result holds "whatever the release
amplitude" while the statement fixes x(0) = 1). Walks the expression with locals for binders and
returns `(bound, roles, fixed)`: `name : type` of data (non-Prop) variables bound by `∀`; for every
explicit argument of an application of a `Checked` constant, `(variable, Def.binder)` when the
argument is a bound variable (its *role*), and `(Def, binder, literal)` when it is a closed numeric
literal (a parameter the statement *fixes*). -/
partial def paramWalk (env : Environment) (e : Expr) (univ : Bool)
    (acc : Array String × Array (String × String) × Array (String × String × String)) :
    MetaM (Array String × Array (String × String) × Array (String × String × String)) := do
  let e := e.consumeMData
  match e with
  | .forallE n d b bi =>
    let mut acc ← paramWalk env d false acc
    -- a hypothesis `f … v = c` with `f` a program definition and `c` closed fixes the last bound
    -- argument `v` (red team H, d04, run 2026-11-04T1428Z: `redshift a t₀ t₃ = 2 * √2 - 1` fixes the
    -- source; a docstring said "every pair of sources in the quasar range"): recorded as the role
    -- `=Def=c` of `v`, read by rule 6 as a parameter fixed to `c`
    let d' := d.consumeMData
    if d'.isAppOfArity ``Eq 3 && !(d'.getArg! 2).hasFVar && !(d'.getArg! 2).hasLooseBVars then
      let lhs := (d'.getArg! 1).consumeMData
      if let .const c _ := lhs.getAppFn then
        if isCheckedConst env c then
          let fv := lhs.getAppArgs.filter (·.consumeMData.isFVar)
          if h : 0 < fv.size then
            let ld ← fv[fv.size - 1].consumeMData.fvarId!.getDecl
            let rhs := toString (← ppExpr (d'.getArg! 2))
            let cs := (c.componentsRev.head!).toString (escape := false)
            acc := (acc.1, acc.2.1.push (ld.userName.eraseMacroScopes.toString (escape := false), s!"={cs}={rhs}"), acc.2.2)
    withLocalDecl n bi d fun x => do
      let isP ← try isProp d catch _ => pure true
      let acc ← if univ && !isP then do
          let ty := toString (← ppExpr d)
          pure (acc.1.push s!"{n.eraseMacroScopes.toString (escape := false)} : {ty}", acc.2)
        else pure acc
      paramWalk env (b.instantiate1 x) univ acc
  | .lam n d b bi =>
    let acc ← paramWalk env d false acc
    -- the binder of a `fun` is not universal (under `∃` it is the witness); `∀` inside its body is
    withLocalDecl n bi d fun x => paramWalk env (b.instantiate1 x) univ acc
  | .letE _ _ v b _ => paramWalk env (b.instantiate1 v) univ (← paramWalk env v false acc)
  | .app .. =>
    let f := e.getAppFn
    let args := e.getAppArgs
    let mut acc := acc
    if let .const c _ := f then
      if isCheckedConst env c then
        if let some ci := env.find? c then
          let bis ← forallTelescopeReducing ci.type fun xs _ => xs.mapM fun x => do
            let ld ← x.fvarId!.getDecl
            return (ld.userName.eraseMacroScopes.toString (escape := false), ld.binderInfo.isExplicit)
          let cs := (c.componentsRev.head!).toString (escape := false)
          for i in [:args.size] do
            if h : i < bis.size then
              let (bn, ex) := bis[i]
              if ex then
                let a := args[i]!.consumeMData
                if a.isFVar then
                  let ld ← a.fvarId!.getDecl
                  acc := (acc.1, acc.2.1.push (ld.userName.eraseMacroScopes.toString (escape := false), s!"{cs}.{bn}"), acc.2.2)
                else if let some l := numLitStr? a then
                  acc := (acc.1, acc.2.1, acc.2.2.push (cs, bn, l))
    -- `∀` inside a conclusion counts through `∧`, `↔`, `→` (above) and inside `∃` bodies (the `∃`
    -- variable itself is not universal) and `¬`; not under `∨` or inside other applications' arguments
    let univArgs := univ && (e.isAppOfArity ``And 2 || e.isAppOfArity ``Iff 2 ||
      e.isAppOf ``Exists || e.isAppOf ``ExistsUnique ||
      -- a refutation `¬ ∀ …` (often a negated claim) generalises over the data of the refuted claim:
      -- its docstring may say "the claim that … holds for every K is false"
      e.isAppOfArity ``Not 1)
    acc ← paramWalk env f false acc
    for a in args do
      acc ← paramWalk env a univArgs acc
    return acc
  | _ => return acc

/-- The `RoundsTo` literals that a statement *asserts*: reached from the conclusion through
`∀` (data binders), `→` (conclusion side only), `∧` and `∃`. A `RoundsTo` under `¬`, `∨`, `↔` or
in a hypothesis is not asserted (red team D, defect D05 certified a number by `¬ RoundsTo`). -/
partial def posRoundsToLits (e : Expr) (acc : Array (Option String) := #[]) : Array (Option String) :=
  match e.consumeMData with
  | .forallE _ _ b _ => posRoundsToLits b acc
  | e =>
    if e.isAppOfArity ``And 2 then posRoundsToLits (e.getArg! 1) (posRoundsToLits (e.getArg! 0) acc)
    else if e.isAppOfArity ``Exists 2 then
      match (e.getArg! 1).consumeMData with
      | .lam _ _ b _ => posRoundsToLits b acc
      | _ => acc
    else if e.isAppOfArity `Checked.Records.RoundsTo 3 then roundsToLits e acc
    else acc

/-- A rational numeral as written (`3 / 10`, `-1 / 2`, `0.245`, `7`) as `(numerator, denominator)`. -/
partial def ratLit? (e : Expr) : Option (Int × Nat) :=
  let e := e.consumeMData
  -- real-valued numerals only (not the ℕ in `ContDiffAt ℝ 6` or `cosmoCoeff 5`)
  if !(e.getAppNumArgs > 0 && (e.getArg! 0).consumeMData.isConstOf ``Real) then none
  else if e.isAppOfArity ``Neg.neg 3 then (ratLit? (e.getArg! 2)).map fun (n, d) => (-n, d)
  else if e.isAppOfArity ``HDiv.hDiv 6 then
    match ratLit? (e.getArg! 4), ratLit? (e.getArg! 5) with
    | some (a, b), some (c, d) => if c > 0 then some (a * d, b * c.toNat) else none
    | _, _ => none
  else match decLit? e with
    | some (neg, m, d) => some ((if neg then -1 else 1) * (m : Int), 10 ^ d)
    | none => none

/-- Every rational numeral in a statement (the parameters a record is stated at). -/
partial def ratLits (e : Expr) (acc : Array (Int × Nat) := #[]) : Array (Int × Nat) :=
  match ratLit? e with
  | some r => acc.push r
  | none =>
    match e with
    | .mdata _ b => ratLits b acc
    | .forallE _ d b _ => ratLits b (ratLits d acc)
    | .lam _ d b _ => ratLits b (ratLits d acc)
    | .letE _ t v b _ => ratLits b (ratLits v (ratLits t acc))
    | .app f a => ratLits a (ratLits f acc)
    | _ => acc

/-- `v=p/q` for every `let v := c` with `c` a rational numeral inside `e` (a record states the
argument a certified quantity is evaluated at as a `let`, run 2026-11-08T0028Z). -/
partial def letBinds (e : Expr) (acc : Array String := #[]) : Array String :=
  match e with
  | .mdata _ b => letBinds b acc
  | .letE n _ v b _ =>
    let acc := match ratLit? v with
      | some (p, q) => acc.push s!"{n.eraseMacroScopes.toString (escape := false)}={p}/{q}"
      | none => letBinds v acc
    letBinds b acc
  | .forallE _ d b _ => letBinds b (letBinds d acc)
  | .lam _ d b _ => letBinds b (letBinds d acc)
  | .app f a => letBinds a (letBinds f acc)
  | _ => acc

/-- The selector of a certified quantity `x` in `RoundsTo x d k` (run 2026-11-08T0028Z; blind red
team T, defect d01 swapped the redshifts of two certified percentages of one record in FINDINGS.md
and every check accepted it, because a record certified values, not the argument the prose attached
to them). Items: `@Def` when the head of `x` is a program definition; `v=p/q` for each explicit
argument of that definition (binder `v`) or of a `fun` head that is a rational numeral; `v=p/q` for
each `let v := p/q` inside `x`. `check_numbers.py` requires a FINDINGS tag of a record with several
certified values to name the selector of the value it tags, `0.56[✓F8_sizes(z=1)]`. -/
def roundsSel (env : Environment) (x : Expr) : String := Id.run do
  let x := x.consumeMData
  let fn := x.getAppFn.consumeMData
  let args := x.getAppArgs
  let mut items : Array String := #[]
  match fn with
  | .const c _ =>
    if isCheckedConst env c then
      items := items.push s!"@{(c.componentsRev.head!).toString (escape := false)}"
      if let some ci := env.find? c then
        let mut ty := ci.type
        let mut i := 0
        while i < args.size do
          match ty with
          | .forallE n _ b bi =>
            if bi.isExplicit then
              if let some (p, q) := ratLit? args[i]! then
                items := items.push s!"{n.eraseMacroScopes.toString (escape := false)}={p}/{q}"
            ty := b
            i := i + 1
          | _ => i := args.size
  | .lam .. =>
    let mut f := fn
    let mut i := 0
    while i < args.size do
      match f with
      | .lam n _ b _ =>
        if let some (p, q) := ratLit? args[i]! then
          items := items.push s!"{n.eraseMacroScopes.toString (escape := false)}={p}/{q}"
        f := b
        i := i + 1
      | _ => i := args.size
  | _ => pure ()
  items := items ++ letBinds x
  return ";".intercalate items.toList

/-- The certified quantities `x` of the asserted `RoundsTo x d k`, pretty-printed (binders of `∀` and `∃`
as locals), in the order of `posRoundsToLits`: the generated table of certified numbers in FINDINGS.md
(run 2026-11-08T0028Z) shows each tag's quantity as Lean states it. -/
partial def posRoundsToXs (e : Expr) : MetaM (Array String) := do
  match e.consumeMData with
  | .forallE n d b bi => withLocalDecl n bi d fun x => posRoundsToXs (b.instantiate1 x)
  | e =>
    if e.isAppOfArity ``And 2 then
      return (← posRoundsToXs (e.getArg! 0)) ++ (← posRoundsToXs (e.getArg! 1))
    else if e.isAppOfArity ``Exists 2 then
      match (e.getArg! 1).consumeMData with
      | .lam n d b bi => withLocalDecl n bi d fun x => posRoundsToXs (b.instantiate1 x)
      | _ => return #[]
    else if e.isAppOfArity `Checked.Records.RoundsTo 3 then
      let str := toString (← ppExpr (e.getArg! 0))
      let str := " ".intercalate (((str.map fun c => if c == '\n' || c == '\t' then ' ' else c).splitOn " ").filter (· != ""))
      return #[str]
    else return #[]

/-- The selectors of the `RoundsTo` conjuncts a statement asserts, in the order of
`posRoundsToLits` (one per asserted `RoundsTo`). -/
partial def posRoundsToSels (env : Environment) (e : Expr) (acc : Array String := #[]) : Array String :=
  match e.consumeMData with
  | .forallE _ _ b _ => posRoundsToSels env b acc
  | e =>
    if e.isAppOfArity ``And 2 then posRoundsToSels env (e.getArg! 1) (posRoundsToSels env (e.getArg! 0) acc)
    else if e.isAppOfArity ``Exists 2 then
      match (e.getArg! 1).consumeMData with
      | .lam _ _ b _ => posRoundsToSels env b acc
      | _ => acc
    else if e.isAppOfArity `Checked.Records.RoundsTo 3 then acc.push (roundsSel env (e.getArg! 0))
    else acc

/-- The conjuncts of a conclusion, looking through `let` (zeta) and program definitions at the head
(`Checked.Trust.unfoldHead`); the flag says whether a `let` or a definition had to be opened. -/
partial def necConjuncts (c : Expr) (hidden : Bool := false) (fuel : Nat := 32) :
    MetaM (Array (Expr × Bool)) := do
  if fuel = 0 then return #[(c, hidden)]
  let c := c.consumeMData
  if c.isLet then
    return ← necConjuncts (c.letBody!.instantiate1 c.letValue!) true (fuel - 1)
  let u ← Checked.Trust.unfoldHead c
  let hidden := hidden || u != c
  if u.isAppOfArity ``And 2 then
    return (← necConjuncts u.appFn!.appArg! hidden (fuel - 1)) ++ (← necConjuncts u.appArg! hidden (fuel - 1))
  if u.consumeMData.isLet then
    return ← necConjuncts u true (fuel - 1)
  return #[(u, hidden)]

/-- Assumptions of a statement that the necessity numbering (binders as written, as CLAIMS.md
numbers them) does not reach, or reaches only formally (blind red team AF, run 2026-11-11T0428Z).
Reasons:
* `conclusion`: after opening a `let` or a program definition, the conclusion (or one of its
  conjuncts) is itself an implication or `∀`: its assumptions are never numbered or classified;
* `subtype`: a binder's type is a subtype (`{x // P x}`, a coerced set): `P` is assumed silently;
* `bundled i`: hypothesis i has two or more parts (`Checked.Trust.partsWalk`: through `∧`, `∃`,
  `∃!`, `∀`, `∀ᶠ` and an implication's conclusion, program definitions unfolded; since run
  2026-11-11T1628Z, blind red team AG, not only a top-level `∧`): necessity is shown for the bundle,
  not for each part, until every part has a witness;
* `restated i`: hypothesis i is a conjunct of the conclusion (literally, or definitionally at default
  transparency since AG d06): it is NEEDED only because
  the conclusion repeats it. -/
def necShape (ty : Expr) : MetaM (Array String) :=
  Checked.Trust.flatStatement ty fun xs c => do
    let mut out : Array String := #[]
    let cs ← necConjuncts c
    if cs.any (fun (e, h) => h && e.consumeMData.isForall) then out := out.push "conclusion"
    let mut sub := false
    for x in xs do
      let t := (← inferType x).consumeMData
      if t.isAppOf ``Subtype || t.isAppOf ``Set.Elem then sub := true
      -- a type defined as a subtype (`NNReal := {r // 0 ≤ r}`) assumes its property just as silently
      -- (blind red team AG d03, run 2026-11-11T1628Z): unfold the type's head at default transparency
      else if !(← isProp t) then
        let w ← withTransparency .default (whnf t)
        if w.isAppOf ``Subtype || w.isAppOf ``Set.Elem then sub := true
    if sub then out := out.push "subtype"
    let ps ← Checked.Trust.hypPositions xs
    for j in [0:ps.size] do
      let t ← inferType xs[ps[j]!]!
      if ← isProp t then
        let u ← Checked.Trust.unfoldHead t
        -- bundled: two or more *parts* (through ∧, ∃, ∃!, ∀, ∀ᶠ and an implication's conclusion,
        -- `Checked.Trust.partsWalk`), not only a top-level `∧` (blind red team AG d01, d02, d05: a
        -- bundle behind `∃ Ω,`, `∀ s, s = t₀ →` or `∃!` was never flagged); a walk that runs out of fuel
        -- counts as bundled
        let m ← try Checked.Trust.numParts t catch _ => pure 2
        if u.isAppOfArity ``And 2 || 2 ≤ m then out := out.push s!"bundled {j+1}"
        -- restated: syntactic, or definitionally equal at default transparency (AG d06: `x ∈ Set.Ioi b`
        -- restating the conclusion `b < x` passed the syntactic test)
        let mut rest := cs.any (fun (e, _) => e == t || e == u)
        unless rest do
          for (e, _) in cs do
            unless rest do
              -- bounded: a failed unfolding race must not stall the trust step
              rest ← try
                  withCurrHeartbeats <| withTheReader Core.Context (fun c => { c with maxHeartbeats := 20000000 })
                    (withTransparency .default (withNewMCtxDepth (isDefEq e t)))
                catch _ => pure false
        if rest then out := out.push s!"restated {j+1}"
    return out

end StatementDeps

open StatementDeps in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  -- candidate non-vacuity witnesses: Checked theorems whose statement is an `∃` or `True`
  let nvCands : Array (Name × Expr) := env.constants.map₁.fold (init := #[]) fun acc n ci =>
    if isCheckedConst env n && !(privateToUserName n).isInternal then
      match ci with
      | .thmInfo t =>
        if t.type.isAppOf ``Exists || t.type.isConstOf ``True then acc.push (n, t.type) else acc
      | _ => acc
    else acc
  -- transcriptions with a machine-checked independent second reading (trust track T3, run 2228Z):
  -- a theorem in `Checked.Trust.Transcriptions` stating `d = e` with `d` a program constant
  -- Since run 2026-11-04T0428Z (red team F, defect F06: `agree_dQFlat : dQFlat = dQFlat := rfl`
  -- earned dQFlat the ² mark with no second reading behind it) the right-hand side must be a
  -- constant of a `Checked.Trust.SecondReading*` module whose statement and body do not reach the
  -- left-hand side; any other theorem in the Transcriptions namespaces is a blocking error.
  let srMod := fun (c : Name) => match env.getModuleIdxFor? c with
    | some idx => ((env.header.moduleNames[idx.toNat]!).toString.startsWith "Checked.Trust.SecondReading")
    | none => false
  let (secondRead, badAgree) : NameSet × Array Name :=
    env.constants.map₁.fold (init := ({}, #[])) fun (acc, bad) n ci =>
    if (`Checked.Trust.Transcriptions).isPrefixOf n && !(privateToUserName n).isInternal then
      match ci with
      | .thmInfo t =>
        match t.type.eq? with
        | some (_, lhs, rhs) =>
          -- an agreement between two propositions (CLAIMs) must be proved without program theorems
          -- (blind red team L of run 2026-11-05T2228Z, d06: two different false claims, the
          -- program's invented formula and a genuine reading of another one, were "equal" by
          -- `propext` of their two refutations); agreements with other agreements stay allowed
          let propOk := match env.find? lhs.constName! with
            | some lc => !lc.type.getForallBody.isProp ||
                t.value.getUsedConstants.all fun c =>
                  -- equation lemmas of definitions (`X.eq_1`, `X.eq_def`; reserved names, generated by
                  -- `unfold X`/`simp only [X]`) and auxiliary proofs that occur in a definition's own
                  -- value (`X._proof_1`) unfold or type-check a definition and are allowed
                  let eqn := (match c with
                    | .str p s => (match env.find? p with
                        | some (.defnInfo d) => s == "eq_def" || s == "eq_unfold" ||
                            (s.startsWith "eq_" && s.length > 3 && (s.toList.drop 3).all Char.isDigit) ||
                            d.value.getUsedConstants.contains c
                        | _ => false)
                    | _ => false)
                  !(isCheckedConst env c && !eqn && (match env.find? c with | some (.thmInfo _) => true | _ => false) &&
                    !(`Checked.Trust.Transcriptions).isPrefixOf c && !(`Checked.Trust.Formulations).isPrefixOf c)
            | none => false
          if lhs.isConst && rhs.isConst && lhs.constName! != rhs.constName! && srMod rhs.constName! && propOk &&
              !(match env.find? rhs.constName! with
                | some rc => (deps env {} (rc.value?.getD (.sort 0)) (deps env {} rc.type {})).contains lhs.constName!
                | none => true) then
            (acc.insert lhs.constName!, bad)
          else (acc, bad.push n)
        | none => (acc, bad.push n)
      | _ => (acc, bad)
    else (acc, bad)
  -- FORMULA definitions with a machine-checked blind second formulation (run 2026-11-05T0828Z;
  -- red team J: d03 put a wrong decimal constant in a FORMULA body, d06 named the JT inversion
  -- temperature `boyleT`; both were accepted because nothing checked a FORMULA's name or docstring
  -- against its body). Same shape as the second readings: a theorem in
  -- `Checked.Trust.Formulations` stating `d = e` with `d` a program constant and `e` a constant of
  -- a `Checked.Trust.SecondFormulation*` module (written blind, from the name, argument roles and
  -- conventions only) whose statement and body do not reach `d`; any other theorem there is a
  -- blocking error.
  let sfMod := fun (c : Name) => match env.getModuleIdxFor? c with
    | some idx => ((env.header.moduleNames[idx.toNat]!).toString.startsWith "Checked.Trust.SecondFormulation")
    | none => false
  let (secondForm, badForm) : NameSet × Array Name :=
    env.constants.map₁.fold (init := ({}, #[])) fun (acc, bad) n ci =>
    if (`Checked.Trust.Formulations).isPrefixOf n && !(privateToUserName n).isInternal then
      match ci with
      | .thmInfo t =>
        match t.type.eq? with
        | some (_, lhs, rhs) =>
          if lhs.isConst && rhs.isConst && lhs.constName! != rhs.constName! && sfMod rhs.constName! &&
              !sfMod lhs.constName! &&
              !(match env.find? rhs.constName! with
                | some rc => (deps env {} (rc.value?.getD (.sort 0)) (deps env {} rc.type {})).contains lhs.constName!
                | none => true) then
            (acc.insert lhs.constName!, bad)
          else (acc, bad.push n)
        | none => (acc, bad.push n)
      | _ => (acc, bad)
    else (acc, bad)
  let mut nNeed := 0
  let mut nWit := 0
  let cands : Array Name := env.constants.map₁.fold (init := #[]) fun acc n _ =>
    if isCheckedConst env n && !(privateToUserName n).isInternal then acc.push n else acc
  let heads ← readLines "scripts/trust/headlines.txt"
  let pinLines ← readLines "scripts/trust/pins.txt"
  let kindLines ← readLines "scripts/trust/def_kinds.txt"
  let mut errors : Array String := #[]
  for n in badAgree do
    errors := errors.push s!"transcription agreement {n} is not `program constant = Checked.Trust.SecondReading* constant` with an independent right-hand side (a second reading must not reach the transcription it checks; an agreement of two propositions must be proved without program theorems: two false claims are equal by propext)"
  for n in badForm do
    errors := errors.push s!"formulation agreement {n} is not `program constant = Checked.Trust.SecondFormulation* constant` with an independent right-hand side (a second formulation must not reach the definition it checks)"
  -- FORMULA definitions still without a second formulation (run 2026-11-05T0828Z); the file may
  -- only shrink (scripts/trust/check_formulas.py --base)
  let formulaBaseLines ← readLines "scripts/trust/formula_baseline.txt"
  -- pins: definition ↦ pinning theorem, checked to mention the definition
  let mut pinned : NameMap Name := {}
  for l in pinLines do
    match l.splitOn " " |>.filter (· ≠ "") with
    | [d, t] =>
      match resolve cands d, resolve cands t with
      | .ok dn, .ok tn =>
        let ty := (env.find? tn).get!.type
        if (deps env {} ty {}).contains dn then pinned := pinned.insert dn tn
        else errors := errors.push s!"pin theorem {tn} does not mention {dn}"
      | .error e, _ => errors := errors.push e
      | _, .error e => errors := errors.push e
    | _ => errors := errors.push s!"bad pins line: {l}"
  let mut kinds : NameMap String := {}
  for l in kindLines do
    match l.splitOn " " |>.filter (· ≠ "") with
    | [d, k] =>
      match resolve cands d with
      | .ok dn => kinds := kinds.insert dn k
      | .error e => errors := errors.push e
    | _ => errors := errors.push s!"bad def_kinds line: {l}"
  let mut formulaBase : NameSet := {}
  for l in formulaBaseLines do
    match resolve cands l with
    | .ok dn =>
      if !(["FORMULA", "MATH", "WITNESS", "PRINTED"].contains ((kinds.find? dn).getD "")) then
        errors := errors.push s!"formula_baseline.txt lists {dn}, which is not of kind FORMULA, MATH, WITNESS or PRINTED"
      else if secondForm.contains dn || secondRead.contains dn then
        errors := errors.push s!"formula_baseline.txt lists {dn}, which now has a blind second formulation: remove the line"
      else formulaBase := formulaBase.insert dn
    | .error e => errors := errors.push s!"formula_baseline.txt: {e}"
  -- grandfathered CLAIMs with inline formulas and no second reading (run 2026-11-05T1428Z)
  let claimBaseLines ← readLines "scripts/trust/claim_baseline.txt"
  let mut claimBase : NameSet := {}
  for l in claimBaseLines do
    match resolve cands l with
    | .ok dn =>
      if (kinds.find? dn) != some "CLAIM" then
        errors := errors.push s!"claim_baseline.txt lists {dn}, which is not of kind CLAIM"
      else if secondRead.contains dn then
        errors := errors.push s!"claim_baseline.txt lists {dn}, which now has a blind second reading: remove the line"
      else claimBase := claimBase.insert dn
    | .error e => errors := errors.push s!"claim_baseline.txt: {e}"
  -- COMPOSITE is "built only from other listed definitions" (run 2026-11-05T0828Z): until now
  -- nothing checked the label, so a free formula labelled COMPOSITE escaped the FORMULA rule above.
  -- A COMPOSITE definition's body may use only program constants that are classified or pinned
  -- (no unlisted helper) and no numeral other than 0 and 1 (arithmetic with constants is a FORMULA).
  for (dn, k) in kinds.toList do
    if k == "COMPOSITE" then
      if let some body := bodyOf env dn then
        let bad := body.getUsedConstants.filter fun c =>
          isCheckedConst env c && reportable env c && c != dn && (kinds.find? c).isNone &&
            !pinned.contains c
        unless bad.isEmpty do
          errors := errors.push s!"COMPOSITE {dn} uses unlisted program definitions {bad.toList}: classify them or reclassify {dn}"
        if let some l := arithNumeral env body then
          errors := errors.push s!"COMPOSITE {dn} contains the numeral {l}: a body with constants is a FORMULA (needs a blind second formulation), not a COMPOSITE"
        if closedArith body || realNumeral body then
          errors := errors.push s!"COMPOSITE {dn} builds a numeric constant by arithmetic on numerals (such as 1 + 1) or passes a numeric constant to a helper: a body with constants is a FORMULA (needs a blind second formulation), not a COMPOSITE"
        -- a COMPOSITE combines listed definitions (red team K, d02: `schwarzschildRadius := G * M / (c * c)`,
        -- a free formula with no program definition in it, passed as COMPOSITE and so needed no second
        -- formulation; its name carried a false factor 2)
        let listed := body.getUsedConstants.filter fun c =>
          isCheckedConst env c && reportable env c && c != dn && ((kinds.find? c).isSome || pinned.contains c)
        if listed.isEmpty then
          errors := errors.push s!"COMPOSITE {dn} uses no listed program definition: a formula in its own variables is a FORMULA (needs a blind second formulation), not a COMPOSITE"
        -- an alias (body: one program definition applied to its arguments and literals) adds a name
        -- and nothing else (red team K of run 2026-11-05T1628Z, d03: `qNought a t := cosmoCoeff 2 a t`,
        -- documented as the deceleration parameter, is minus it; adversary of run 1428Z: an alias
        -- named as physics): state the definition directly
        if let some (.defnInfo d) := env.find? dn then
          let core := d.value.getLambdaBody
          if let .const c _ := core.getAppFn then
            if c != dn && isCheckedConst env c && core.getAppArgs.all (fun a => a.isBVar || a.isAppOfArity ``OfNat.ofNat 3 || a.isRawNatLit) then
              errors := errors.push s!"COMPOSITE {dn} is an alias of {c} (its body only applies {c} to its arguments and literals): use {c} in the statement; an alias's name and docstring are read by no check"
  -- the kind label must be one of the documented kinds (run 2026-11-05T0828Z: an unknown label such
  -- as `FOO` was silently treated as checked); a SPEC must be the spec of at least one pin (else
  -- the label hides a free formula); a CLAIM's body may use only classified or pinned program
  -- definitions.
  let pinSpecs : NameSet := pinned.foldl (init := {}) fun acc _ tn =>
    (deps env {} (env.find? tn).get!.type {}).foldl (init := acc) fun a c =>
      if kinds.find? c == some "SPEC" then a.insert c else a
  for (dn, k) in kinds.toList do
    unless ["PHYSICS", "PRINTED", "CLAIM", "FORMULA", "COMPOSITE", "SPEC", "WITNESS", "MATH"].contains k do
      errors := errors.push s!"def_kinds.txt: {dn} has the unknown kind {k}"
    if k == "SPEC" && !pinSpecs.contains dn then
      errors := errors.push s!"SPEC {dn} is used by no pinning theorem (pins.txt): a SPEC label is earned by pinning a definition"
    if k == "CLAIM" then
      -- a claim is a proposition (run 2026-11-05T0828Z judge: `boyleT := 2a/(Rb)` labelled CLAIM
      -- passed the body rule, having no program definition in its body)
      let isPropTy ← liftTermElabM <| forallTelescope (env.find? dn).get!.type fun _ b => return b.isProp
      unless isPropTy do
        errors := errors.push s!"CLAIM {dn} is not a proposition: a CLAIM states a source's claim (Prop); a formula is a FORMULA"
      if let some body := bodyOf env dn then
        let bad := body.getUsedConstants.filter fun c =>
          isCheckedConst env c && reportable env c && c != dn && (kinds.find? c).isNone && !pinned.contains c
        unless bad.isEmpty do
          errors := errors.push s!"CLAIM {dn} uses unlisted program definitions {bad.toList}: classify them"
        -- a CLAIM that writes its formula inline (numerals, constants built from numerals) is a
        -- transcription of the source like a PRINTED definition (run 2026-11-05T1428Z, blind red team K,
        -- d06: an invented "l₀ = 1 + 3Ω + 27Ω²" attributed to a real paper passed as CLAIM with no second
        -- reading): it needs a machine-checked blind second reading (Checked/Trust/Transcriptions*.lean)
        -- or a line of scripts/trust/claim_baseline.txt (grandfathered; shrink-only, check_formulas.py)
        if ((arithNumeral env body).isSome || closedArith body || realNumeral body || inlineArith env body || litConclusion body) && !secondRead.contains dn &&
            !claimBase.contains dn then
          errors := errors.push s!"CLAIM {dn} writes its formula inline (numerals) with no machine-checked blind second reading of the source (Checked/Trust/Transcriptions*.lean): an inline formula attributed to a source is a transcription"
  let mut formulaReached : NameSet := {}
  let stop : NameSet := pinned.foldl (init := {}) fun s n _ => s.insert n
  -- pin shape (run 0028Z; red-team defect B03 "pinned" a definition by restating it): the pin
  -- theorem's statement must use a SPEC-kind definition whose own type and body do not mention
  -- the definition being pinned.
  -- Load-bearing positions only (red team C, defect C02 put the spec in a decorative conjunct):
  -- the head of a hypothesis, or the head of a side of the conclusion when it is `=` or `↔`.
  for (dn, tn) in pinned.toList do
    let ty := (env.find? tn).get!.type
    -- heads of a proposition: under its `∀`s, the head, or the heads of both sides of `=`/`↔`
    let propHeads (p : Expr) (withHead : Bool) : MetaM (Array Name) := forallTelescope p fun _ b => do
      let sides := match b.eq? with
        | some (_, l, r) => #[l, r]
        | none => match b.iff? with
          | some (l, r) => #[l, r]
          | none => if withHead then #[b] else #[]
      return sides.filterMap (·.getAppFn.constName?)
    let heads : Array Name ← liftTermElabM <| forallTelescope ty fun xs concl => do
      let mut hs : Array Name := #[]
      for x in xs do
        let d ← inferType x
        if ← isProp d then hs := hs ++ (← propHeads d true)
      return hs ++ (← propHeads concl false)
    let specs := heads.toList.filter fun s =>
      kinds.find? s == some "SPEC" &&
        let sc := (env.find? s).get!
        !(deps env {} (sc.value?.getD (.sort 0)) (deps env {} sc.type {})).contains dn
    if specs.isEmpty then
      errors := errors.push s!"pin {tn} for {dn} uses no SPEC-kind definition independent of {dn} (a restatement of the definition is not a pin)"
  -- frozen registry (run 0028Z): headlines, pins, pinned and classified definitions may not change
  -- (statement, or statement and body) unless `scripts/trust/frozen.txt` is updated, which CI
  -- allows only with a LEDGER.md entry naming the constant (scripts/trust/check_relock.py).
  let mut frozenNow : NameMap String := {}
  -- the plain-words docstrings of headlines and pinned definitions are frozen too (run 1028Z; red
  -- team E: E02 reversed the sign convention in the docstring of the pinned `decel`, E04 turned a
  -- refutation's docstring into an endorsement, E06 generalised a record's docstring; a docstring
  -- is what a scientist reads, so changing it needs a LEDGER line like any frozen change)
  let docFp := fun (n : Name) => do
    return s!"-doc{hash ((← findDocString? env n).getD "")}"
  for h in heads do
    if let .ok hn := resolve cands h then
      frozenNow := frozenNow.insert hn (fingerprint (env.find? hn).get! ++ (← docFp hn))
  for (dn, tn) in pinned.toList do
    frozenNow := frozenNow.insert dn (fingerprint (env.find? dn).get! ++ (← docFp dn))
    frozenNow := frozenNow.insert tn (fingerprint (env.find? tn).get!)
  for (dn, k) in kinds.toList do
    -- the kind label is frozen too (red team C, defect C07 relabelled PRINTED as FORMULA)
    let d ← if pinned.contains dn then docFp dn else pure ""
    frozenNow := frozenNow.insert dn (fingerprint (env.find? dn).get! ++ d ++ "-" ++ k)
    -- run 2026-11-04T0428Z (red team F: F01 rewrote the docstring of the FORMULA `critCubic` into a
    -- false general claim, F02 the field docstrings of the SPEC `MaxwellSpec`; both are printed in
    -- the validation packet and were not frozen): the docstring of every classified definition and
    -- of each field of a classified structure is frozen as its own entry `doc:<name>` (so the
    -- existing entries keep their fingerprints); a change needs relock + a LEDGER line naming it
    unless pinned.contains dn do
      let mut fd ← docFp dn
      if isStructure env dn then
        for f in getStructureFieldsFlattened env dn (includeSubobjectFields := false) do
          fd := fd ++ (← docFp (dn ++ f))
      frozenNow := frozenNow.insert (Name.mkSimple ("doc:" ++ dn.toString)) fd
  -- module docstrings (`/-! … -/`) of every Checked module are frozen too, entry `moduledoc:<module>`
  -- (red team F, defect F04: the module doc of `B1Fit` overstated the range of least-squares fits)
  for m in env.header.moduleNames do
    if m.getRoot == `Checked then
      let docs := (getModuleDoc? env m).getD #[]
      unless docs.isEmpty do
        frozenNow := frozenNow.insert (Name.mkSimple ("moduledoc:" ++ m.toString))
          s!"-mdoc{hash (String.intercalate "\n" (docs.toList.map (·.doc)))}"
  -- run 2026-11-04T1028Z (red team G: d05 rewrote the docstring of the pin theorem
  -- `criticalSpec_pins` to drop its smoothness hypothesis, d06 transposed the digits of the proved
  -- window in the docstring of the lemma `reduced_window`; neither docstring was frozen or read):
  -- the docstring of EVERY Checked declaration is frozen, entry `doc:<name>` (the entries above win)
  for (n, _) in env.constants.map₁.toList do
    if let some idx := env.getModuleIdxFor? n then
      if (env.header.moduleNames[idx.toNat]!).getRoot == `Checked && !n.isInternal then
        let key := Name.mkSimple ("doc:" ++ n.toString)
        let docIn := ((frozenNow.find? n).map fun f => decide ((f.splitOn "-doc").length > 1)).getD false
        unless frozenNow.contains key || docIn do
          if let some d ← findDocString? env n then
            frozenNow := frozenNow.insert key s!"-doc{hash d}"
  let frozenLines := (frozenNow.toList.toArray.qsort (fun a b => a.1.toString < b.1.toString)).map
    fun (n, f) => s!"{n.toString (escape := false)} {f}"
  if (← IO.getEnv "TRUST_RELOCK") == some "1" then
    IO.FS.writeFile "scripts/trust/frozen.txt" (String.intercalate "\n" ([
      "# Frozen fingerprints (statement; for definitions statement + body) of every headline, pin",
      "# theorem, pinned and classified definition. Generated: TRUST_RELOCK=1 lake env lean",
      "# scripts/trust/StatementDeps.lean. Changing or removing a line needs a LEDGER.md entry",
      "# naming the constant in the same push (CI: scripts/trust/check_relock.py). Run 0028Z."] ++
      frozenLines.toList) ++ "\n")
    logInfo m!"frozen.txt rewritten ({frozenLines.size} entries)"
  else
    let lockLines ← readLines "scripts/trust/frozen.txt"
    let mut locked : Std.HashMap String String := {}
    for l in lockLines do
      match l.splitOn " " |>.filter (· ≠ "") with
      | [n, f] => locked := locked.insert n f
      | _ => errors := errors.push s!"bad frozen.txt line: {l}"
    for (n, f) in frozenNow.toList do
      match locked.get? (n.toString (escape := false)) with
      | some f' =>
        if f != f' then
          errors := errors.push s!"FROZEN {n} changed (statement or definition body): if intended, relock (TRUST_RELOCK=1) and name it in a LEDGER.md entry"
      | none => errors := errors.push s!"{n} is not in scripts/trust/frozen.txt: relock (TRUST_RELOCK=1)"
    -- an entry that is no longer registered was removed without relocking (red team C)
    let nowStr : Std.HashSet String := frozenNow.foldl (init := {}) fun s n _ => s.insert (n.toString (escape := false))
    for (n, _) in locked.toList do
      unless nowStr.contains n do
        errors := errors.push s!"FROZEN {n} is no longer registered (headline, pin or kind removed): relock and name it in a LEDGER.md entry"
  -- Checked may import only Checked and libraries, never the drafts in `Work` (red team C, defect
  -- C04 hid a wrong constant in a Work module that a Checked headline imported)
  for m in env.header.moduleNames do
    if m.getRoot == `Work then
      errors := errors.push s!"Checked imports the draft module {m}: Work is not checked"
  -- unused hypotheses (T2b level 0) in headlines and pin theorems
  for h in heads ++ (pinned.toList.map (·.2.toString)).toArray do
    if let .ok hn := resolve cands h then
      let ci := (env.find? hn).get!
      if let .thmInfo t := ci then
        let us ← liftTermElabM <| unusedHyps t.type t.value
        -- a hypothesis that is a conjunction is checked per binder only, so a partly used
        -- conjunct goes unnoticed (red team C, defect C06): hypotheses must be curried
        let conj ← liftTermElabM <| forallTelescope t.type fun xs _ => do
          let mut out : Array Name := #[]
          for x in xs do
            let d ← instantiateMVars (← inferType x)
            if d.consumeMData.isAppOfArity ``And 2 then out := out.push (← x.fvarId!.getUserName)
          return out
        unless conj.isEmpty do
          errors := errors.push s!"{hn}: hypotheses {conj.toList} are conjunctions; state each conjunct as its own hypothesis (so the unused-hypothesis check sees each)"
        unless us.isEmpty do
          errors := errors.push s!"{hn}: hypotheses {us.toList} are never used by the proof: the statement claims less than is proved (drop them)"
  -- records (run 0028Z; red-team defect A07): a Checked theorem cited in STATE.md "Results" must be
  -- a registered headline, so that it is subject to every check above.
  -- (whole STATE.md and FINDINGS.md: red team C, defect C05 cited one under a new heading)
  let results := (← IO.FS.readFile "STATE.md") ++ "\n" ++ (← IO.FS.readFile "FINDINGS.md")
  let headSet : NameSet := heads.foldl (init := {}) fun s h =>
    match resolve cands h with | .ok hn => s.insert hn | .error _ => s
  let toks := (results.splitOn "`").toArray.zipIdx.filterMap fun (t, i) =>
    if i % 2 == 1 && !t.contains ' ' && !t.isEmpty then some t else none
  let mut nCited := 0
  for t in toks do
    -- `name[_suffix]` cites name and name_suffix
    let variants := match t.splitOn "[" with
      | [a, r] => match r.splitOn "]" with
        | [b, c] => [a ++ c, a ++ b ++ c]
        | _ => [t]
      | _ => [t]
    for v in variants do
      let thms := cands.filter fun n =>
        (n.toString == v || n.toString.endsWith ("." ++ v)) &&
        (env.find? n matches some (.thmInfo _))
      -- a dotted name in an existing Checked namespace that names nothing (red team D, defect D08
      -- cited invented theorems as if proved)
      if v.contains '.' && !v.contains '/' && !v.contains ' ' && !v.endsWith ".lean" && !v.endsWith ".md"
          && !v.endsWith ".txt" && !v.endsWith ".py" && !v.endsWith ".png" then
        let comps := v.splitOn "."
        let pre := ".".intercalate (comps.take (comps.length - 1))
        let anyHit := cands.any fun n => n.toString == v || n.toString.endsWith ("." ++ v)
        let nsExists := !pre.isEmpty && cands.any fun n =>
          let ns := n.toString
          ns.startsWith (pre ++ ".") || (ns.splitOn ("." ++ pre ++ ".")).length > 1
        if nsExists && !anyHit then
          errors := errors.push s!"STATE.md/FINDINGS.md cite `{v}`: no such constant in Checked (namespace {pre} exists)"
      if thms.size == 1 then
        nCited := nCited + 1
        -- exempt: pure-mathematics lemmas whose statement uses no program definition
        let pure := ((deps env {} (env.find? thms[0]!).get!.type {}).toList.filter (reportable env)).isEmpty
        unless headSet.contains thms[0]! || pure do
          errors := errors.push s!"STATE.md/FINDINGS.md cite {thms[0]!}, which is not in scripts/trust/headlines.txt (unregistered headlines escape every check)"
  logInfo m!"records: {nCited} theorem citations in STATE.md and FINDINGS.md checked against headlines.txt"
  -- certified numbers (run 2026-10-31T0228Z; red-team defects A06, B07 changed numbers in
  -- FINDINGS.md and every check accepted them): every headline in `Checked.Records` states
  -- `RoundsTo x d k`; its decimals are written to `.lake/records_numbers.tsv`, against which
  -- `scripts/trust/check_numbers.py` checks every `[✓name]` tag in FINDINGS.md.
  let mut recLines : Array String := #[]
  let mut parLines : Array String := #[]
  for h in heads do
    if let .ok hn := resolve cands h then
      if (`Checked.Records).isPrefixOf hn then
        let lits := posRoundsToLits (env.find? hn).get!.type
        if lits.isEmpty then
          errors := errors.push s!"{hn} is in Checked.Records but asserts no RoundsTo"
        if (roundsToLits (env.find? hn).get!.type).size != lits.size then
          errors := errors.push s!"{hn}: a RoundsTo in a position the statement does not assert (under ¬, ∨, ↔ or in a hypothesis)"
        for (n, d) in ratLits (env.find? hn).get!.type do
          parLines := parLines.push s!"{hn.componentsRev.head!}\t{n}/{d}"
        let sels := posRoundsToSels env (env.find? hn).get!.type
        let xs ← liftTermElabM <| posRoundsToXs (env.find? hn).get!.type
        for (l, j) in lits.zipIdx do
          -- third column: the selector of the certified quantity; fourth: the quantity as Lean prints it
          -- (run 2026-11-08T0028Z)
          let sel := if sels.size == lits.size then sels[j]! else ""
          let xq := if xs.size == lits.size then xs[j]! else ""
          match l with
          | some str => recLines := recLines.push s!"{hn.componentsRev.head!}\t{str}\t{sel}\t{xq}"
          | none => errors := errors.push s!"{hn}: a RoundsTo whose value is not a decimal literal with at most k decimals"
  IO.FS.createDirAll ".lake"
  IO.FS.writeFile ".lake/records_numbers.tsv" (String.intercalate "\n" recLines.toList ++ "\n")
  IO.FS.writeFile ".lake/records_params.tsv" (String.intercalate "\n" parLines.toList ++ "\n")
  logInfo m!"certified numbers: {recLines.size} RoundsTo literals in Checked.Records headlines"
  let mut gapCount : NameMap Nat := {}
  let mut unclassified : NameSet := {}
  let mut rows : Array String := #[]
  let mut nHeads := 0
  let mut nClean := 0
  for h in heads do
    match resolve cands h with
    | .error e => errors := errors.push e
    | .ok hn =>
      nHeads := nHeads + 1
      let ci := (env.find? hn).get!
      unless ci matches .thmInfo _ do errors := errors.push s!"{hn} is not a theorem"
      let (nw, ob) ← liftTermElabM do
        return (← Checked.Trust.needsWitness ci.type, ← Checked.Trust.nvObligation ci.type)
      let mut nvCol := "unconditional"
      if nw then
        nNeed := nNeed + 1
        -- prefer the witness named after the headline; a witness of another headline with the
        -- same obligation is shown as such (pilot validation, run 2026-10-31T0828Z: the bare name
        -- of another theorem in this column misled reviewers)
        let same := fun (n : Name) => n.componentsRev.head!.toString.endsWith hn.componentsRev.head!.toString
        let found := (nvCands.find? (fun (n, t) => n != hn && t == ob && same n)).orElse
          fun _ => nvCands.find? (fun (n, t) => n != hn && t == ob)
        match found with
        | some (w, _) =>
          nWit := nWit + 1
          nvCol := if same w then s!"`{w.componentsRev.head!}`"
            else s!"`{w.componentsRev.head!}` (shared: same obligation)"
        | none =>
          nvCol := "**MISSING**"
          errors := errors.push s!"{hn}: no non-vacuity witness (a Checked theorem stating `nonvacuity% {hn}`)"
      let ds := (deps env stop ci.type {}).toList.filter (reportable env) |>.toArray.qsort
        (·.toString < ·.toString)
      let mut pins : Array String := #[]
      let mut gaps : Array String := #[]
      let mut transcr : Array String := #[]
      let mut lines : Array String := #[]
      for d in ds do
        let k := match pinned.find? d with
          | some _ => "PINNED"
          | none => (kinds.find? d).getD "UNCLASSIFIED"
        lines := lines.push s!"    {k} {d}"
        let short := d.componentsRev.head!.toString
        if k == "PINNED" then pins := pins.push short
        else if k == "PHYSICS" || k == "UNCLASSIFIED" then
          gaps := gaps.push short
          gapCount := gapCount.insert d ((gapCount.find? d).getD 0 + 1)
          errors := errors.push s!"{hn} rests on the unpinned {k} definition {d}: pin it (pins.txt) or classify it (def_kinds.txt)"
          if k == "UNCLASSIFIED" then unclassified := unclassified.insert d
        else if k == "PRINTED" || k == "CLAIM" then
          transcr := transcr.push (if secondRead.contains d then short ++ "²" else short)
          -- a PRINTED label without a second reading hid a free formula (run 2026-11-05T0828Z): the
          -- second reading is now required like the second formulation (baseline: same file)
          if k == "PRINTED" && !secondRead.contains d && !formulaBase.contains d then
            errors := errors.push s!"{hn} rests on the PRINTED definition {d} with no machine-checked blind second reading (Checked/Trust/Transcriptions*.lean)"
        else if ["FORMULA", "MATH", "WITNESS"].contains k then
          formulaReached := formulaReached.insert d
          unless secondForm.contains d || formulaBase.contains d do
            errors := errors.push s!"{hn} rests on the {k} definition {d} with no machine-checked blind second formulation (Checked/Trust/Formulations*.lean): its name and docstring are unchecked (red team J, d03/d06)"
      if gaps.isEmpty then nClean := nClean + 1
      let shortH := (hn.toString.replace "Checked.Cosmography." "").replace "Checked." ""
      let fmt (a : Array String) : String := if a.isEmpty then "—" else ", ".intercalate a.toList
      -- parameters the statement fixes to numbers, generated (rule 6, run 2026-11-04T1428Z): a reader
      -- sees what the statement does not generalise over, whatever the docstring says
      let expTy0 ← liftCoreM <| Meta.deltaExpand ci.type fun n => isCheckedConst env n && !stop.contains n
      let (_, rl, fx) ← liftTermElabM do
        let a ← paramWalk env ci.type true (#[], #[], #[])
        paramWalk env expTy0 true a
      let fx := fx.toList.eraseDups
      let fdefs := (fx.map (·.1)).eraseDups
      -- variables fixed by an equation hypothesis `f … v = c` (role `=f=c`), shown as `f(v) = c`
      let eqs := (rl.toList.filter (·.2.startsWith "=")).eraseDups.map fun (v, r) =>
        match (r.drop 1).toString.splitOn "=" with
        | f :: rest => s!"{f}({v}) = {"=".intercalate rest}"
        | [] => r
      let parts := (fdefs.map fun d =>
        s!"{d}: " ++ ", ".intercalate ((fx.filter (·.1 == d)).map fun (_, b, l) => s!"{b} = {l}")) ++ eqs
      let fixedCol := if parts.isEmpty then "—" else "; ".intercalate parts
      rows := rows.push s!"| `{shortH}` | {fmt pins} | {fmt gaps} | {fmt transcr} | {nvCol} | {fixedCol} |"
      logInfo m!"{hn}\n{String.intercalate "\n" lines.toList}"
  -- meaning carried by prose (trust track T2c, run 2026-10-31T1028Z; red-team defects A04, B04,
  -- A05, D04 were accepted by every check because their meaning lived in names and docstrings):
  -- for every headline and every non-pinned definition a headline reaches, write the docstring,
  -- the statement's logical shape and the pinned definitions it actually reaches (through
  -- formulas, composites and claims) to `.lake/meaning.jsonl`; `scripts/trust/check_prose.py`
  -- checks the docstrings and names against them (glossary `scripts/trust/glossary.txt`).
  let mut mlines : Array String := #[]
  -- laws of pinned predicates: equations in their bodies that mention a pinned definition
  let lawSk : Array (Name × String) := pinned.foldl (init := #[]) fun acc d _ =>
    match env.find? d with
    | some (.defnInfo dv) => (collectEqs dv.value).foldl (init := acc) fun acc q =>
        if q.getUsedConstants.any (fun c => stop.contains c && c != d) then acc.push (d, eqSkeleton q) else acc
    | _ => acc
  let mut defUsers : NameMap (Array Name) := {}
  for h in heads do
    if let .ok hn := resolve cands h then
      let ci := (env.find? hn).get!
      -- shape and quantifiers are read after unfolding the program's own non-pinned definitions
      -- (claims, formulas, composites): `¬ Claim` with `Claim := ∀ …` is about every model
      let expTy ← liftCoreM <| Meta.deltaExpand ci.type fun n => isCheckedConst env n && !stop.contains n
      let (univ, shapes) ← liftTermElabM <| stmtShape expTy
      let (pBound, pRoles, pFixed) ← liftTermElabM do
        let a ← paramWalk env expTy true (#[], #[], #[])
        paramWalk env ci.type true a
      let reached := (deps env stop ci.type {}).toList
      let pinsR := reached.filter (stop.contains ·)
      let others := reached.filter fun d => !stop.contains d && reportable env d
      for d in others do
        defUsers := defUsers.insert d (((defUsers.find? d).getD #[]).push hn)
      -- junk values (run 2026-11-05T1428Z; blind red team K, d04: `a t = 0 → redshift a t₀ t = -1`, true
      -- only because Lean sets x/0 = 0, read as "light from the Big Bang has z = −1" under the pinned
      -- phrase of `redshift`): a headline may not assume a quantity is zero and divide by it (after
      -- unfolding every program definition, pinned ones included)
      let fullTy ← liftCoreM <| Meta.deltaExpand ci.type fun n => isCheckedConst env n
      let junk ← liftTermElabM <| forallTelescope fullTy fun xs body => do
        let mut zeros : Array Expr := #[]
        for x in xs do
          let t ← inferType x
          if let some (_, l, r) := t.eq? then
            if isZeroLit r then zeros := zeros.push l
            if isZeroLit l then zeros := zeros.push r
        let dens := (denominators body).foldl (fun acc d => denomFactors d acc) #[]
        (zeros.filter fun z => dens.contains z).mapM fun z => return toString (← ppExpr z)
      unless junk.isEmpty do
        errors := errors.push s!"{hn} assumes {junk.toList} = 0 and divides by it: its conclusion is about Lean's junk value x / 0 = 0, outside the domain of every pinned meaning (red team K, d04)"
      let doc := (← findDocString? env hn).getD ""
      let sks := (collectEqs expTy).map eqSkeleton
      let laws := (lawSk.filter fun (_, k) => sks.contains k).map (·.1) |>.toList.eraseDups
      let modName := match env.getModuleIdxFor? hn with
        | some idx => toString (env.header.moduleNames[idx.toNat]!)
        | none => ""
      mlines := mlines.push (Json.mkObj [("type", "headline"), ("name", toString hn), ("module", modName),
        ("laws", toJson (laws.map toString)),
        ("doc", doc), ("universal", univ), ("shapes", toJson shapes),
        ("nums", toJson (statementNums ci.type).toList.eraseDups),
        ("bound", toJson pBound.toList.eraseDups),
        ("roles", Json.arr (pRoles.toList.eraseDups.toArray.map fun (v, r) => Json.arr #[Json.str v, Json.str r])),
        ("fixed", Json.arr (pFixed.toList.eraseDups.toArray.map fun (d, b, l) =>
          Json.mkObj [("def", d), ("param", b), ("lit", l)])),
        ("record", (`Checked.Records).isPrefixOf hn),
        -- conjuncts that assert a certified number but reach no pinned or transcribed definition
        -- (red team E, defect E05 put a free formula next to a genuine pinned conjunct)
        ("free_conjuncts", toJson ((topConjuncts ci.type).filter (fun c =>
            !(roundsToLits c).isEmpty &&
            !((deps env stop c {}).toList.any fun d => stop.contains d ||
              (kinds.find? d) == some "PRINTED" || (kinds.find? d) == some "CLAIM"))).size),
        ("pinned", toJson (pinsR.map toString)),
        ("defs", Json.mkObj (others.map fun d => (toString d, Json.str ((kinds.find? d).getD "UNCLASSIFIED"))))]).compress
  for (d, users) in defUsers.toList do
    let dc := (env.find? d).get!
    let own := (deps env stop (dc.value?.getD (.sort 0)) (deps env stop dc.type {})).toList.filter (stop.contains ·)
    let doc := (← findDocString? env d).getD ""
    mlines := mlines.push (Json.mkObj [("type", "def"), ("name", toString d),
      ("kind", (kinds.find? d).getD "UNCLASSIFIED"), ("doc", doc),
      ("pinned", toJson (own.map toString)), ("users", toJson (users.map toString))]).compress
  for (d, _) in pinned.toList do
    mlines := mlines.push (Json.mkObj [("type", "pinned"), ("name", toString d)]).compress
  IO.FS.writeFile ".lake/meaning.jsonl" (String.intercalate "\n" mlines.toList ++ "\n")
  logInfo m!"meaning: {mlines.size} entries written to .lake/meaning.jsonl"
  let summary := gapCount.toList.toArray.qsort (fun a b => a.2 > b.2)
  let summaryLines := summary.toList.map fun (n, k) => s!"| `{n}` | {k} |"
  let printedDefs := kinds.toList.filter (fun (_, k) => k == "PRINTED")
  let nPrinted := printedDefs.length
  let nSecond := (printedDefs.filter fun (d, _) => secondRead.contains d).length
  let formulaDefs := kinds.toList.filter (fun (_, k) => ["FORMULA", "MATH", "WITNESS"].contains k)
  let nFormula := formulaDefs.length
  let nFormSecond := (formulaDefs.filter fun (d, _) => secondForm.contains d).length
  let formulaLines := (formulaDefs.map (·.1)).toArray.qsort (·.toString < ·.toString) |>.toList.map fun d =>
    let st := if secondForm.contains d then "²" else if formulaBase.contains d then "baselined (no second formulation yet)" else "—"
    let used := if formulaReached.contains d then "yes" else "no"
    s!"| `{d}` | {st} | {used} |"
  -- hypothesis necessity (trust track T2b level 1, run 2026-11-09T0628Z; `Checked/Trust/NonVacuity.lean`,
  -- `necessity%`, `dropped%`): every hypothesis of every headline is classified as NEEDED (a Checked
  -- theorem states `necessity% h i`: data meeting every other hypothesis with the conclusion false),
  -- REDUNDANT (a Checked theorem states `dropped% h i`: the same statement without it), DATA (a later
  -- binder or the conclusion uses its proof; no obligation) or OPEN. Reported, not yet blocking (annex LIV).
  let mut thmByHash : Std.HashMap UInt64 (Array (Name × Expr)) := {}
  for (n, ci) in env.constants.map₁.toList do
    if isCheckedConst env n && !(privateToUserName n).isInternal then
      if let .thmInfo t := ci then
        thmByHash := thmByHash.insert t.type.hash ((thmByHash.getD t.type.hash #[]).push (n, t.type))
  let findThm := fun (e : Expr) (avoid : Name) =>
    ((thmByHash.getD e.hash #[]).find? fun (n, t) => n != avoid && t == e).map (·.1)
  let mut necLines : Array String := #[]
  let mut necTsv : Array String := #[]
  let mut nHyp : Nat := 0
  let mut nNeeded : Nat := 0
  let mut nRedundant : Nat := 0
  let mut nDataH : Nat := 0
  let mut nHeadAll : Nat := 0
  let mut nHeadHyp : Nat := 0
  for h in heads do
    if let .ok hn := resolve cands h then
      let ci := (env.find? hn).get!
      let k ← liftTermElabM <| Checked.Trust.numHyps ci.type
      let shape0 ← liftTermElabM <| necShape ci.type
      -- per-part necessity of a bundled hypothesis (runs 2026-11-11T1428Z, 1628Z; T2b item 3e from blind
      -- red team AF): `bundled i` is dropped when every part of hypothesis i (`Checked.Trust.partsWalk`:
      -- through ∧, ∃, ∀, ∀ᶠ and an implication's conclusion) is NEEDED (a Checked theorem states
      -- `necessity% h i j`) or REDUNDANT (`dropped% h i j`); the witnesses are listed in a `parts of i (m)`
      -- part. Partial coverage is not reported and `bundled i` stays.
      let mut shape : Array String := #[]
      let mut conjParts : Array String := #[]
      for item in shape0 do
        if item.startsWith "bundled " then
          let i := (item.drop 8).toNat!
          let m ← liftTermElabM <| Checked.Trust.numHypParts ci.type i
          let mut cNeed : Array String := #[]
          let mut cRed : Array String := #[]
          let mut allDone := 2 ≤ m
          for j in [1:m+1] do
            let obs ← liftTermElabM do
              try
                return some (← Checked.Trust.necPartObligation ci.type i j, ← Checked.Trust.dropPartObligation ci.type i j)
              catch _ => return none
            match obs with
            | none => allDone := false
            | some (ne, dr) =>
              match findThm ne hn with
              | some w => cNeed := cNeed.push s!"{j} (`{w.componentsRev.head!}`)"
              | none =>
                match findThm dr hn with
                | some w => cRed := cRed.push s!"{j} (`{w.componentsRev.head!}`)"
                | none => allDone := false
          if allDone then
            unless cNeed.isEmpty do
              conjParts := conjParts.push s!"parts of {i} ({m}) needed {", ".intercalate cNeed.toList}"
            unless cRed.isEmpty do
              conjParts := conjParts.push (s!"parts of {i} ({m}) " ++
                (if cRed.size ≥ 2 then "redundant (each alone, not together) " else "redundant ") ++
                ", ".intercalate cRed.toList)
          else shape := shape.push item
        else shape := shape.push item
      let shortH := (hn.toString.replace "Checked.Cosmography." "").replace "Checked." ""
      let shapePart := if shape.isEmpty then [] else [s!"shape: {", ".intercalate shape.toList}"]
      if k == 0 then
        unless shape.isEmpty do
          necLines := necLines.push (s!"- `{shortH}` (0): " ++ "; ".intercalate shapePart)
        continue
      nHeadHyp := nHeadHyp + 1
      let mut needed : Array String := #[]
      let mut redund : Array String := #[]
      let mut dataH : Array String := #[]
      let mut openH : Array String := #[]
      for i in [1:k+1] do
        nHyp := nHyp + 1
        let obs ← liftTermElabM do
          try
            return some (← Checked.Trust.necObligation ci.type i, ← Checked.Trust.dropObligation ci.type i)
          catch _ => return none
        match obs with
        | none =>
          nDataH := nDataH + 1
          dataH := dataH.push s!"{i}"
          necTsv := necTsv.push s!"{hn}\t{i}\tDATA\t-"
        | some (ne, dr) =>
          match findThm ne hn with
          | some w =>
            nNeeded := nNeeded + 1
            needed := needed.push s!"{i} (`{w.componentsRev.head!}`)"
            necTsv := necTsv.push s!"{hn}\t{i}\tNEEDED\t{w}"
          | none =>
            match findThm dr hn with
            | some w =>
              nRedundant := nRedundant + 1
              redund := redund.push s!"{i} (`{w.componentsRev.head!}`)"
              necTsv := necTsv.push s!"{hn}\t{i}\tREDUNDANT\t{w}"
            | none =>
              openH := openH.push s!"{i}"
              necTsv := necTsv.push s!"{hn}\t{i}\tOPEN\t-"
      if openH.size == 0 && dataH.size == 0 && shape.isEmpty then nHeadAll := nHeadAll + 1
      let part := fun (lbl : String) (a : Array String) =>
        if a.isEmpty then [] else [s!"{lbl} {", ".intercalate a.toList}"]
      necLines := necLines.push (s!"- `{shortH}` ({k}): " ++ "; ".intercalate
        (part "needed" needed ++ part (if redund.size ≥ 2 then "redundant (each alone, not together)" else "redundant") redund ++ part "no obligation (instance, or proof used as data)" dataH ++ part "open" openH ++ conjParts.toList ++ shapePart))
  IO.FS.writeFile ".lake/necessity.tsv" (String.intercalate "\n" necTsv.toList ++ "\n")
  logInfo m!"hypothesis necessity: {nHyp} hypotheses of {nHeadHyp} headlines; needed {nNeeded}, redundant {nRedundant}, no obligation {nDataH}, open {nHyp - nNeeded - nRedundant - nDataH}"
  let md := String.intercalate "\n" ([
    "# TRUST MAP (generated by `scripts/trust/StatementDeps.lean`; do not edit by hand)",
    "",
    "For each headline theorem: the program-written definitions its *statement* rests on",
    "(transitively; proofs are checked by the kernel and not listed). A definition is",
    "**pinned** when a machine-checked specification determines it (trust track T1);",
    "**unpinned physics** definitions are the weakest unchecked steps; **transcriptions**",
    "(printed formulas, source claims) rest on reading the source correctly (trust track T3).",
    "Pure formulas, series templates, remainders and specs are omitted from the table.",
    "",
    s!"Headlines: {nHeads}. Resting on no unpinned physics definition: {nClean}.",
    s!"Non-vacuity (trust track T2): {nNeed} headlines have hypotheses; {nWit} of them have a",
    "machine-checked witness that all their hypotheses hold at once (`Checked/Trust/Witnesses.lean`,",
    "obligation computed from the statement by `Checked.Trust.nvObligation`); the others are",
    "unconditional (binders are plain data only).",
    s!"Hypothesis necessity (trust track T2b, run 2026-11-09T0628Z): {nHyp} hypotheses in {nHeadHyp} headlines;",
    s!"{nNeeded} shown NEEDED (a machine-checked example meeting every other hypothesis where the conclusion fails),",
    s!"{nRedundant} shown REDUNDANT in Lean (the same statement proved without it), {nDataH} with no obligation (instance arguments, proofs used as data),",
    s!"{nHyp - nNeeded - nRedundant - nDataH} open; headlines with every hypothesis classified: {nHeadAll}/{nHeadHyp}",
    "(section \"Hypothesis necessity\" below; obligations `necessity%`, `dropped%` in `Checked/Trust/NonVacuity.lean`).",
    s!"Transcriptions (trust track T3): {nPrinted} PRINTED definitions; {nSecond} carry a machine-checked",
    "agreement with an independent blind second reading (`Checked/Trust/Transcriptions.lean`; marked ² below).",
    s!"FORMULA, MATH and WITNESS definitions with a blind second formulation: {nFormSecond}/{nFormula} (run 2026-11-05T0828Z;",
    "² on a FORMULA means a machine-checked agreement with a blind second formulation in",
    "`Checked/Trust/Formulations*.lean`, written from the definition's name, argument roles and conventions",
    "without its body; a headline may rest on such a definition without one only if it is listed in",
    "`scripts/trust/formula_baseline.txt`, which may only shrink).",
    "",
    "## Unpinned physics definitions, by number of headlines resting on them",
    "",
    "| Definition | Headlines |",
    "|---|---|"] ++ summaryLines ++ [
    "",
    "## Per headline",
    "",
    "Last column (generated from the statement, run 2026-11-04T1428Z): the explicit arguments of program",
    "definitions that the statement fixes to numbers, and variables a hypothesis `f(v) = c` fixes. The result is proved for these values only, whatever",
    "the docstring says; universally bound parameters are not listed.",
    "",
    "| Headline | Pinned | Unpinned physics | Transcriptions | Non-vacuity witness | Fixed by the statement |",
    "|---|---|---|---|---|---|"] ++ rows.toList ++ [
    "",
    "## Hypothesis necessity, per headline",
    "",
    "Hypotheses are numbered as in CLAIMS.md (\"assuming 1., 2., …\"). NEEDED: a Checked theorem states",
    "`necessity% <headline> i` (some data meet every other hypothesis and the conclusion is false: without",
    "hypothesis i the statement is false). REDUNDANT: a Checked theorem states `dropped% <headline> i` (the",
    "statement holds in Lean without hypothesis i). Redundancy is shown one hypothesis at a time, never for",
    "several together, and in Lean's total arithmetic (x / 0 = 0, √ of a negative number = 0, log 0 = 0), so",
    "a hypothesis that only excludes such a value can be redundant here and still matter on paper. Open:",
    "neither is proved yet. Shape (run 2026-11-11T0428Z, blind red team AF): assumptions the numbering does",
    "not reach or reaches only formally — `conclusion` (after opening a `let` or a program definition the",
    "conclusion contains an implication or `∀` whose assumptions are not numbered), `subtype` (a binder of",
    "subtype type assumes its property silently), `bundled i` (hypothesis i has two or more parts, see below:",
    "shown needed as a bundle only), `restated i` (hypothesis i is also a conjunct of the conclusion, literally",
    "or after unfolding definitions: needed only because the conclusion repeats it). A headline with a shape entry never counts",
    "as having every hypothesis classified, and a new one fails CI (`check_necessity.py` N4). Two or more",
    "redundant hypotheses of one headline are labelled \"each alone, not together\": dropping them all may make",
    "the statement false (red team AF d02). Parts (runs 2026-11-11T1428Z, 1628Z): `bundled i` is dropped once every",
    "part of hypothesis i is NEEDED (`necessity% <headline> i j`: every other hypothesis holds and hypothesis i",
    "holds with part j replaced by `True`, the conclusion fails) or REDUNDANT (`dropped% <headline> i j`). The",
    "parts are the maximal sub-propositions reached through `∧`, `∃ x,`, `∀ x,`, `∀ᶠ x in l,` and the conclusion",
    "of an implication, with program definitions unfolded (`Checked.Trust.partsWalk`); an implication's premise,",
    "`∨`, `↔` and `¬` are not entered. The witnesses are listed as `parts of i (m)`, m the number of parts.",
    ""] ++ necLines.toList ++ [
    "",
    "## FORMULA, MATH and WITNESS definitions (second formulation)",
    "",
    "| Definition | Second formulation | Reached by a headline |",
    "|---|---|---|"] ++ formulaLines) ++ "\n"
  IO.FS.writeFile "TRUST_MAP.md" md
  logInfo m!"SUMMARY: {nHeads} headlines; {nClean} rest on no unpinned physics definition; \
    non-vacuity: {nWit}/{nNeed} conditional headlines witnessed.\n\
    {String.intercalate "\n" (summary.toList.map fun (n, k) => s!"  {k}  {n}")}"
  unless unclassified.isEmpty do
    logInfo m!"UNCLASSIFIED (add to scripts/trust/def_kinds.txt): {unclassified.toList}"
  -- Checked must not change how statements are displayed (red team K, d01, run 2026-11-05T1628Z:
  -- a global `@[app_unexpander LE.le]` in a new Checked module printed every `≤` of CLAIMS.md and
  -- TRUST_MAP as `<`; the kernel statements were unchanged, so no other check saw it). Blocking:
  -- (1) any unexpander or delaborator that a Checked module makes active for importers
  -- (`notation`/`infix` declared globally or `scoped` and opened, `@[app_unexpander]`, `@[delab]`;
  -- `local notation` is not exported and is allowed), and (2) any Checked constant whose type is
  -- meta-level code (`Lean.*`, `IO`: initializers, macros, elaborators, parsers), which could
  -- change the printer at import time, outside the module that defines `nonvacuity%`.
  let metaOk : Name := `Checked.Trust.NonVacuity
  let modOf := fun (c : Name) => match env.getModuleIdxFor? c with
    | some idx => env.header.moduleNames[idx.toNat]!
    | none => .anonymous
  let unexp := (Lean.PrettyPrinter.Delaborator.appUnexpanderAttribute.ext.getState env).table.toList
  let delab := (Lean.PrettyPrinter.Delaborator.delabAttribute.ext.getState env).table.toList
  let unexpN : List (Name × List Name) := unexp.map fun (k, l) =>
    (k, l.map fun (e : KeyedDeclsAttribute.AttributeEntry Lean.PrettyPrinter.Unexpander) => e.declName)
  let delabN : List (Name × List Name) := delab.map fun (k, l) =>
    (k, l.map fun (e : KeyedDeclsAttribute.AttributeEntry Lean.PrettyPrinter.Delaborator.Delab) => e.declName)
  for (key, es) in unexpN ++ delabN do
    for dn in es do
      if isCheckedConst env dn then
        errors := errors.push s!"{dn} (module {modOf dn}) changes how `{key}` is printed in every generated claim (unexpander/delaborator active for importers; red team K, d01): Checked may not change the printer"
  -- (private meta-level constants are what `local notation` generates; they cannot reach importers,
  -- so only their IO-typed ones, initializers, count)
  for (n, ci) in env.constants.map₁.toList do
    if isCheckedConst env n && modOf n != metaOk then
      let roots : List Name := if isPrivateName n then [`IO, `EIO, `BaseIO] else [`Lean, `IO, `EIO, `BaseIO]
      if ci.type.getUsedConstants.any (fun c => roots.contains c.getRoot) then
        errors := errors.push s!"{n} (module {modOf n}) is meta-level code (type {ci.type.getUsedConstants.toList.filter (fun c => [`Lean, `IO, `EIO, `BaseIO].contains c.getRoot)}): Checked modules other than {metaOk} may not define macros, elaborators, parsers, printers or initializers (red team K, d01)"
  unless errors.isEmpty do
    throwError m!"statement-dependency registry errors:\n{String.intercalate "\n" errors.toList}"
