/-- Value of a closed real numeral (run 2026-11-26T0828Z, parametric closures): a term built from `OfNat.ofNat`,
`OfScientific.ofScientific`, `Neg.neg`, `Inv.inv`, `HAdd.hAdd`, `HSub.hSub`, `HMul.hMul`, `HDiv.hDiv` and `HPow.hPow`
with a natural-number literal exponent, every type argument `ℝ` and every instance argument built only from
constants of Lean or Mathlib (a program module could declare its own `OfNat ℝ 7` instance). `none` otherwise. -/
partial def realNumVal? (env : Environment) (e : Expr) : Option ℚ := do
  let e := e.consumeMData
  if e.hasLooseBVars || e.hasFVar || e.hasMVar then none
  let isR := fun (t : Expr) => t.consumeMData == mkConst ``Real
  -- a theorem (e.g. the proof `d._proof_1 : Nat.AtLeastTwo 3` Lean abstracts out of a definition) carries no data
  let libInst := fun (i : Expr) => i.getUsedConstants.all fun c =>
    match env.find? c with
    | some (.thmInfo _) => true
    | _ => match env.getModuleIdxFor? c with
      | some idx => (env.header.moduleNames[idx.toNat]!).getRoot != `Checked
      | none => false
  let natLit? : Expr → Option ℕ := fun n => match n.consumeMData with
    | .lit (.natVal k) => some k
    | x => if x.isAppOfArity ``OfNat.ofNat 3 then
        match x.appFn!.appArg!.consumeMData with | .lit (.natVal k) => some k | _ => none
      else none
  let f := e.getAppFn
  let args := e.getAppArgs
  match f with
  | .const ``OfNat.ofNat _ =>
    guard (args.size == 3 && isR args[0]! && libInst args[2]!)
    let k ← natLit? args[1]!
    return ((k : ℕ) : ℚ)
  | .const ``OfScientific.ofScientific _ =>
    guard (args.size == 5 && isR args[0]! && libInst args[1]!)
    let m ← natLit? args[2]!
    let ex ← natLit? args[4]!
    match args[3]!.consumeMData with
    | .const ``Bool.true _ => return (m : ℚ) / (10 : ℚ) ^ ex
    | .const ``Bool.false _ => return (m : ℚ) * (10 : ℚ) ^ ex
    | _ => none
  -- casts of natural and integer literals (red team BB, run 2026-11-26T0828Z: `(1e-9 : ℝ) * ((3321992119 : ℕ) : ℝ)`
  -- re-spelt a literal past the check of kept numerals)
  | .const ``Nat.cast _ =>
    guard (args.size == 3 && isR args[0]! && libInst args[1]!)
    let k ← natLit? args[2]!
    return ((k : ℕ) : ℚ)
  | .const ``Int.cast _ =>
    guard (args.size == 3 && isR args[0]! && libInst args[1]!)
    let z := args[2]!.consumeMData
    if z.isAppOfArity ``Neg.neg 3 then return - (((← natLit? z.appArg!) : ℕ) : ℚ)
    return (((← natLit? z) : ℕ) : ℚ)
  | .const ``Neg.neg _ =>
    guard (args.size == 3 && isR args[0]! && libInst args[1]!)
    return - (← realNumVal? env args[2]!)
  | .const ``Inv.inv _ =>
    guard (args.size == 3 && isR args[0]! && libInst args[1]!)
    return (← realNumVal? env args[2]!)⁻¹
  | .const n _ =>
    guard (args.size == 6 && isR args[0]! && libInst args[3]!)
    if n == ``HPow.hPow then
      guard (args[1]!.consumeMData == mkConst ``Nat && isR args[2]!)
      let k ← natLit? args[5]!
      return (← realNumVal? env args[4]!) ^ k
    guard (isR args[1]! && isR args[2]!)
    let a ← realNumVal? env args[4]!
    let b ← realNumVal? env args[5]!
    if n == ``HAdd.hAdd then return a + b
    else if n == ``HSub.hSub then return a - b
    else if n == ``HMul.hMul then return a * b
    else if n == ``HDiv.hDiv then return a / b
    else none
  | _ => none

/-- A literal of a headline that a parametric closure varies: a maximal closed real numeral whose value is neither 0
nor 1 (those are structural: `0 < x`, `p → 1`). -/
def isVariedLit (env : Environment) (e : Expr) : Bool :=
  match realNumVal? env e with
  | some q => q != 0 && q != 1
  | none => false

/-- Number of varied literals of `h` (maximal: a varied literal is not entered). -/
partial def countVaried (env : Environment) (h : Expr) : Nat :=
  let h := h.consumeMData
  if isVariedLit env h then 1 else
  if (realNumVal? env h).isSome then 0 else
  match h with
  | .app f a => countVaried env f + countVaried env a
  | .lam _ t b _ => countVaried env t + countVaried env b
  | .forallE _ t b _ => countVaried env t + countVaried env b
  | .letE _ t v b _ => countVaried env t + countVaried env v + countVaried env b
  | .proj _ _ b => countVaried env b
  | _ => 0

/-- `h` is `y` with every varied literal of `h` replaced by one of the variables `vars`, each used once; `st` records
which literal each variable stands for. -/
partial def matchVaried (env : Environment) (vars : Array Expr) (h y : Expr) (st : Array (Option Expr)) :
    Option (Array (Option Expr)) := do
  let h := h.consumeMData
  let y := y.consumeMData
  if isVariedLit env h then
    let j ← vars.findIdx? (· == y)
    guard st[j]!.isNone
    return st.set! j (some h)
  if (realNumVal? env h).isSome then
    guard (h == y); return st
  match h, y with
  | .app f a, .app g b => matchVaried env vars a b (← matchVaried env vars f g st)
  | .lam _ t b _, .lam _ t' b' _ => matchVaried env vars b b' (← matchVaried env vars t t' st)
  | .forallE _ t b _, .forallE _ t' b' _ => matchVaried env vars b b' (← matchVaried env vars t t' st)
  | .letE _ t v b _, .letE _ t' v' b' _ =>
    matchVaried env vars b b' (← matchVaried env vars v v' (← matchVaried env vars t t' st))
  | .proj s i b, .proj s' i' b' => do guard (s == s' && i == i'); matchVaried env vars b b' st
  | _, _ => do guard (h == y); return st

/-- Every closed real numeral replaced by a marker of its value (`7.5` and `15 / 2` become the same term). -/
def normNumerals (env : Environment) (e : Expr) : Expr :=
  e.replace fun s => (realNumVal? env s).map fun q => .lit (.strVal s!"ℝ:{q}")

/-- The blind reader's own definitions (those `isReading` accepts) unfolded, so that a closure may write a reader's
helper (`blindModulus d := 5 * Real.logb 10 d`) inline and vary its literals. -/
def unfoldReader (env : Environment) (isReading : Name → Bool) (e : Expr) : Expr := Id.run do
  let mut e := e
  for _ in [0:8] do
    let e' := e.replace fun s =>
      match s.getAppFn with
      | .const c ls =>
        if isReading c then
          match env.find? c with
          | some (.defnInfo d) => some ((d.value.instantiateLevelParams d.levelParams ls).beta s.getAppArgs)
          | _ => none
        else none
      | _ => none
    if e' == e then break
    e := e'
  return e

/-- The real numerals of `e` (values). -/
def numeralValues (env : Environment) (e : Expr) : Array ℚ := Id.run do
  let mut out : Array ℚ := #[]
  let mut stack : Array Expr := #[e]
  while !stack.isEmpty do
    let s := stack.back!.consumeMData
    stack := stack.pop
    if let some q := realNumVal? env s then out := out.push q; continue
    match s with
    | .app f a => stack := (stack.push f).push a
    | .lam _ t b _ => stack := (stack.push t).push b
    | .forallE _ t b _ => stack := (stack.push t).push b
    | .letE _ t v b _ => stack := ((stack.push t).push v).push b
    | .proj _ _ b => stack := stack.push b
    | _ => pure ()
  return out

/-- Every proof inside a statement replaced by one marker (proof irrelevance: a statement's meaning does not depend on
which proof of an instance side condition it carries; the closure bench of run 2026-11-26T0828Z found a reading whose
`ContinuousSMul ℝ ℝ` proof Lean had abstracted to `HomannSol._proof_1`, written in full in the closure). -/
def eraseProofs (e : Expr) : MetaM Expr :=
  Meta.transform e (pre := fun s => do
    let p ← try isProof s catch _ => pure false
    return if p then .done (.lit (.strVal "proof")) else .continue)

/-- Parametric closure of a fidelity objection (run 2026-11-26T0828Z; replaces the rule of test AZ, which a red team
beat by inlining the program's own proof, run 2026-11-26T0228Z). Let `c₀ = (c₀₁, …, c₀ₙ)` be the varied literals of
the headline `H` (maximal closed real numerals other than 0 and 1, left to right) and `H[c]` the headline with them
replaced by variables. The closure theorem `t` must state `∀ c₁ … cₙ : ℝ, X ↔ H[c]` (each variable standing for one
literal, any order), where `X` at the headline's values is the body of the blind reading `rn` (a `def rn : Prop` of a
`Checked.Trust.SecondReading*` module) up to the value of its real numerals; and `t.bite` must prove
`¬ ∀ c₁ … cₙ : ℝ, H[c]` (the literals bite). Both on the standard axioms. Then `X c ↔ H[c]` holds at every value,
including values where `H[c]` is false: an equivalence of truth values only at the certified literals (`True ↔ H`,
or the program's proof inlined, red team BA) cannot be stated, since `∀ c, True ↔ H[c]` contradicts the bite. The
proof may use any theorem: the statement, not the proof, carries the meaning. -/
def paramClosureFaults (env : Environment) (isReading : Name → Bool) (head t rn : Name) :
    MetaM (Array String) := do
  let some ci := env.find? t | return #[s!"closure theorem {t} not found"]
  let some hc := env.find? head | return #[s!"headline {head} not found"]
  let .thmInfo tv := ci | return #[s!"{t} is not a theorem"]
  let hty ← eraseProofs hc.type.consumeMData
  let n := countVaried env hty
  if n == 0 then
    return #[s!"{head} has no real literal other than 0 and 1: a parametric closure cannot vary it, so no closure of an objection on it is accepted"]
  let mut bad : Array String := #[]
  -- the reading
  let body? : Option Expr := match env.find? rn with
    | some (.defnInfo d) => if isReading rn && d.type.consumeMData.isProp then some d.value else none
    | _ => none
  if body?.isNone then
    bad := bad.push s!"{rn} is not a `def … : Prop` of a `Checked.Trust.SecondReading*` module (a blind reader's statement)"
  -- the closure's statement
  let r ← forallBoundedTelescope tv.type (some n) fun vars body => do
    if vars.size != n then return (some s!"{t} must quantify over {n} real variables, one for each literal of {head}", none)
    for v in vars do
      unless (← inferType v).consumeMData == mkConst ``Real do
        return (some s!"the variables of {t} must be real numbers", none)
    let body := body.consumeMData
    unless body.isAppOfArity ``Iff 2 do return (some s!"{t} does not state `∀ c, X ↔ H[c]`", none)
    let x ← eraseProofs body.appFn!.appArg!.consumeMData
    let y ← eraseProofs body.appArg!.consumeMData
    match matchVaried env vars hty y (Array.replicate n none) with
    | none => return (some s!"the right side of {t} is not the statement of {head} with each of its {n} literals replaced by one of the variables", none)
    | some st =>
      if st.any (·.isNone) then return (some s!"a variable of {t} stands for no literal of {head}", none)
      if y != x && (x.find? (· == y)).isSome then
        return (some s!"the reading side of {t} contains the headline's statement itself", none)
      -- every numeral the left side keeps has a value none of the headline's literals has (red team residue, run
      -- 2026-11-26T0828Z: `(a = 2 ∧ b = 3) ∨ b > a`, a case split true at the literals, holds the headline at them)
      let lits := (st.map (·.get!)).filterMap (realNumVal? env)
      if (numeralValues env (unfoldReader env isReading x)).any (lits.contains ·) then
        return (some s!"the left side of {t} keeps a numeral equal to a literal of {head} (every occurrence of a literal's value must be a variable)", none)
      let x0 := x.replaceFVars vars (st.map (·.get!))
      return (none, some x0)
  match r with
  | (some f, _) => bad := bad.push f
  | (none, some x0) =>
    if let some b := body? then
      let lhs ← eraseProofs (unfoldReader env isReading x0)
      let rhs ← eraseProofs (unfoldReader env isReading b)
      unless x0.consumeMData == mkConst rn || normNumerals env lhs == normNumerals env rhs do
        bad := bad.push s!"the left side of {t} at the literals of {head} is not the reading {rn}"
  | _ => pure ()
  -- the bite
  match env.find? (t ++ `bite) with
  | some (.thmInfo bv) =>
    let ok ← do
      let bt := bv.type.consumeMData
      if !bt.isAppOfArity ``Not 1 then pure false else
      forallBoundedTelescope bt.appArg! (some n) fun vars body => do
        if vars.size != n then return false
        for v in vars do
          unless (← inferType v).consumeMData == mkConst ``Real do return false
        match matchVaried env vars hty (← eraseProofs body) (Array.replicate n none) with
        | some st => return st.all (·.isSome)
        | none => return false
    unless ok do bad := bad.push s!"{t ++ `bite} does not state `¬ ∀ c, H[c]` for {head}"
  | _ => bad := bad.push s!"no theorem {t ++ `bite} stating that the literals of {head} bite (`¬ ∀ c, H[c]`)"
  -- axioms
  for c in [t, t ++ `bite] do
    if (env.find? c).isSome then
      for a in ← collectAxioms c do
        unless a == ``propext || a == ``Classical.choice || a == ``Quot.sound do
          bad := bad.push s!"{c} uses the axiom {a}"
  return bad
