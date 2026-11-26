import Checked

/-!
# Generated claims (trust track T2c/T5, run 2026-11-04T2228Z)

Writes `CLAIMS.md`: for every headline of `scripts/trust/headlines.txt`, its claim **generated
mechanically from the Lean statement**, so that what a reader relies on is not hand-written.

Why (blind red teams F, G, H, I of runs 2026-11-04T0428Z–1428Z: 32 of 32 wrong claims accepted,
almost all as correct theorems carrying false prose): pattern rules on docstrings (check_prose.py)
were beaten every round by a new construction. A rendering of the statement itself cannot
overstate it.

Rendering (deterministic, no model involved):
* the leading binders become "For every …" (data) and a numbered list of assumptions (`Prop`
  binders); the remaining proposition is the conclusion;
* logical structure is spelled out in words: `∧` "and", `∨` "or", `¬` "it is false that",
  `↔` "if and only if", `→` "if … then …", `∀` "for every", `∃` "there is", `∃!` "there is exactly
  one"; top-level conjunctions of the conclusion become a numbered list;
* an application of a PINNED `Prop`-valued definition is replaced by its phrase from
  `scripts/trust/phrases.txt` with the actual arguments substituted (the phrase is the only
  hand-written text; it is frozen and linted by `check_claims.py`);
* every other atom is printed verbatim by Lean's pretty-printer in a code span (program names
  shortened to a suffix that is unique in this file);
* every program definition the statement reaches is listed: PINNED ones with their phrase, pin
  theorem and their full body, all others with their kind and their full body (Prop-valued bodies
  rendered in words).

After blind round W (run 2026-11-08T1428Z, d04: `expansionRate := |hubble|` registered with the phrase
"the Hubble rate a′(t)/a(t)"), run 2026-11-08T1828Z: a phrase is author text, so the body of every
pinned definition is now printed from Lean right after its phrase, and phrases contain no formula
(rule P1 of `check_claims.py`; U2: a phrase's first glossary term belongs to its own definition). Every
formula a reader sees in a generated claim is printed by Lean.
The author's docstring is shown last, labelled as an unchecked paraphrase.

Status line (run 2026-11-18T0228Z, `runs/2026-11-18T0228Z/t5/READERS.md`): under every headline, its module and the
axioms `Lean.collectAxioms` returns (any axiom beyond `propext`, `Classical.choice`, `Quot.sound` is a blocking
error), and the rule that a headline is withdrawn only by leaving `Checked` and the registry. Blind readers took a
hand-written withdrawal over a silent generated page 6/6; with the line, 0/6 answered "no" and 6/6 "unclear".
`check_claim_vocab.py` and `check_numbers.py` skip the line (control G1 in `controls/prose_rule_controls.py`).
Fidelity record (run 2026-11-18T0828Z, `runs/2026-11-18T0828Z/t5/`): the same line also lists, per headline, the
non-vacuity witness, hypothesis necessity counts (computed as in StatementDeps.lean), the registered blind literal
readings and grandfathered literals, and the freeze; after blind readers kept the kernel status and still declined to
cite a valid headline over a hand-written *fidelity* objection.

After blind red team J (run 2026-11-04T2228Z, `runs/2026-11-04T2228Z/t5/RESULTS.md`; designed after
reading it): leading data binders that fill slots of pinned definitions are renamed to the slot
name (author's name shown) unless they are a decorated form of it (`t₀`, `v₁`, `v'`); omitted proofs are
printed with their statement; objects defined by `Classical.choose` are explained by the property
they are chosen to satisfy; terms with truncating ℕ/ℤ arithmetic are printed with numeral types and
flagged; formula bodies with decimal constants are flagged; two reached definitions whose names are
equal up to primes are a blocking error.

Blocking errors: a headline that does not resolve; a pinned definition reached by a headline with
no phrase; a phrase whose placeholder is not a binder name of its definition.

Run: `lake env lean scripts/trust/Claims.lean` (after `lake build Checked`); CI fails when the
committed `CLAIMS.md` differs from the generated one.
-/

open Lean Meta Elab Command

namespace Claims

def isCheckedConst (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some idx => (env.header.moduleNames[idx.toNat]!).getRoot == `Checked
  | none => false

/-- Program constants a term rests on, transitively through bodies (not entering `stop`). -/
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

/-- Closure of a fidelity objection (run 2026-11-25T2028Z, test AZ, `runs/2026-11-25T2028Z/t5/RESULTS_AZ.md`): an
entry of `objections.txt` may carry a fifth field `closed by <theorem>`. The theorem must state `R ↔ H` (or `H ↔ R`)
with `H` the headline's statement (syntactically, or up to reducible unfolding) and `R` a definition of a
`Checked.Trust.SecondReading*` module (a blind reader's statement of the source claim: the blind-route, brief-leak
and provenance checks of those modules apply to it), and its proof may use no theorem of the program: every
constant the proof reaches is followed through the program's definitions, and a program constant whose type is a
proposition (a theorem, a proof stored as a definition) fails the closure, except the closure theorem's own
compiler-generated auxiliaries (internal names under it). Two proved propositions are always equivalent
(`iff_of_true`); this rule is what makes the equivalence a statement about meaning: it has to hold by unfolding and
by Mathlib, not because both sides are proved by the program. `isProg` says which constants are the program's
(`isCheckedConst` on the page; the controls below pass their own namespace).
Run 2026-11-26T0228Z (closure bench, `runs/2026-11-26T0228Z/t5/RESULTS_BENCH.md`): the first version rejected 6/6
honest closures of real headlines, all through proofs Lean abstracts out of definitions (`d._proof_n`, e.g.
`(9 + 1).AtLeastTwo` for a numeral 10), one also through an equation lemma (`d.eq_1`, from `rw [d]`) and one through
Mathlib-only helper lemmas. Those three kinds are now followed instead of rejected (their statements and proofs under
the same rules, their proofs scanned by the closed-subterm rule); a helper counts as the closure's own only when it is
named `<closure theorem>.<name>` (one component more) and declared in the closure's module (red team BA). -/
def closureFaults (env : Environment) (isProg : Name → Bool) (isReading : Name → Bool) (head t : Name) :
    MetaM (Array String) := do
  let some ci := env.find? t | return #[s!"closure theorem {t} not found"]
  let some hc := env.find? head | return #[s!"headline {head} not found"]
  let .thmInfo tv := ci | return #[s!"{t} is not a theorem"]
  let mut bad : Array String := #[]
  let ty := tv.type.consumeMData
  if !ty.isAppOfArity ``Iff 2 then
    return #[s!"{t} does not state an equivalence `R ↔ H`"]
  let a := ty.appFn!.appArg!.consumeMData
  let b := ty.appArg!.consumeMData
  let hty := hc.type.consumeMData
  let isH := fun (e : Expr) => do
    if e == hty then return true
    withReducible (isDefEq e hty)
  let other? ← if ← isH b then pure (some a) else if ← isH a then pure (some b) else pure none
  match other? with
  | none => bad := bad.push s!"neither side of {t} is the statement of {head}"
  | some r =>
    match r.consumeMData with
    | .const rn _ =>
      if rn == head then bad := bad.push s!"the reading side of {t} is the headline itself"
      else if !isReading rn then
        bad := bad.push s!"the reading {rn} of {t} is not a definition of a `Checked.Trust.SecondReading*` module"
      else match env.find? rn with
        | some (.defnInfo _) => pure ()
        | _ => bad := bad.push s!"the reading {rn} of {t} is not a definition"
    | _ => bad := bad.push s!"the reading side of {t} is not a named definition (a blind reader's `def … : Prop`)"
  -- the proof uses no theorem of the program. Followed, not rejected (run 2026-11-26T0228Z, closure bench
  -- `runs/2026-11-26T0228Z/t5/`: the rule as first shipped rejected 6/6 honest closures of real headlines through
  -- these alone): a proof Lean abstracts out of a definition's body (`d._proof_n`, `_auxLemma`: e.g.
  -- `(9 + 1).AtLeastTwo` for the numeral 10 in any definition), an equation lemma of a definition (`d.eq_1`,
  -- `d.eq_def`, made by `rw [d]` or `unfold d`), and the closure's own helpers (theorems named `<t>.<name>`). Each is
  -- part of a definition's text or of the closure's own text, not a theorem of the program's library; its proof and
  -- its statement are followed under the same rules, and its proof is scanned by the closed-subterm rule below.
  let isAux := fun (c : Name) => match c with
    | .str _ s => s.startsWith "_proof_" || s.startsWith "_auxLemma"
    | _ => false
  let mut todo : Array Name := tv.value.getUsedConstants
  let mut seen : NameSet := {}
  let mut followed : Array Expr := #[]
  while !todo.isEmpty do
    let c := todo.back!
    todo := todo.pop
    if seen.contains c || c == t then continue
    seen := seen.insert c
    unless isProg c do continue
    let some cc := env.find? c | continue
    let isP ← isProp cc.type
    -- an equation lemma of a definition (`isEqnThm` misses the ones `rw [d]` realizes; the name is enough, since a
    -- followed constant is checked all the way down under the same rules)
    let isEqn := match c with
      | .str d s => (Lean.Meta.isEqnReservedNameSuffix s || s == "eq_def" || s == "eq_unfold") &&
          (match env.find? d with | some (.defnInfo _) => true | _ => false)
      | _ => false
    -- the closure's own helper: exactly one name component below the closure theorem, in the closure's own module
    -- (red team BA, run 2026-11-26T0228Z: with `t.isPrefixOf c`, a closure theorem named `Checked` made every theorem
    -- of the program its own helper; two forged closures of real headlines passed)
    let ownHelper := (match c with | .str p _ => p == t | _ => false) &&
      env.getModuleIdxFor? c == env.getModuleIdxFor? t
    let follow := isAux c || ownHelper || isEqn
    if isP && !follow then
      bad := bad.push s!"the proof of {t} uses the program's theorem {c} (a closure must hold by unfolding and Mathlib; a helper of the closure itself must be named `{t}.<name>`)"
      continue
    if isP then
      todo := todo ++ cc.type.getUsedConstants
      if let some v := cc.value? (allowOpaque := true) then followed := followed.push v
    match cc with
    | .defnInfo d => todo := todo ++ d.value.getUsedConstants
    | .thmInfo d => todo := todo ++ d.value.getUsedConstants
    | .opaqueInfo d => todo := todo ++ d.value.getUsedConstants
    | _ => pure ()
  -- no closed subterm of the proof is a proof of either side (`iff_of_true p q` with `p`, `q` re-proved from
  -- Mathlib alone; a bridge by unfolding, reordering or rewriting proves `R ↔ H` without proving `R` or `H`)
  if let some r := other? then
    let sides := #[hty, r]
    let mut subs : Std.HashSet Expr := {}
    let mut stack : Array Expr := #[tv.value] ++ followed
    while !stack.isEmpty do
      let e := stack.back!
      stack := stack.pop
      if subs.contains e then continue
      subs := subs.insert e
      match e with
      | .app f x => stack := (stack.push f).push x
      | .lam _ d b _ => stack := (stack.push d).push b
      | .forallE _ d b _ => stack := (stack.push d).push b
      | .letE _ t v b _ => stack := ((stack.push t).push v).push b
      | .mdata _ b => stack := stack.push b
      | .proj _ _ b => stack := stack.push b
      | _ => pure ()
    let mut hit := false
    for e in subs.toArray do
      if hit then break
      if e.hasLooseBVars || e.isSort || e.isMVar then continue
      let ok ← try
          let ty ← inferType e
          if !(← isProp ty) then pure false
          else sides.anyM fun s => do
            if ty.consumeMData == s then return true
            withReducible (isDefEq ty s)
        catch _ => pure false
      if ok then
        bad := bad.push s!"the proof of {t} contains a proof of one side by itself (a closure must relate the two sides, not prove them)"
        hit := true
  return bad

/-- Value of a closed real numeral (run 2026-11-26T0828Z, parametric closures; `runs/2026-11-26T0828Z/t5/RESULTS_PARAM.md`): a term built from `OfNat.ofNat`,
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

def reportable (env : Environment) (n : Name) : Bool :=
  !(privateToUserName n).isInternal && !(Lean.Meta.isMatcherCore env n) && !env.isProjectionFn n &&
  match env.find? n with
  | some (.defnInfo _) => true
  | some (.inductInfo _) => true
  | _ => false

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

structure Ctx where
  pinned : NameMap Name
  kinds : NameMap String
  phrases : NameMap String
  /-- certified phrase lines (rule P13, run 2026-11-09T1828Z): definition ↦ (reader line, theorem) -/
  certs : NameMap (Array (String × Name)) := {}
  /-- full name ↦ displayed name, longest full names first -/
  short : Array (String × String)

/-- Collapse whitespace (the pretty-printer breaks long lines). -/
def oneLine (s : String) : String :=
  " ".intercalate ((s.split (fun c => c == '\n' || c == ' ')).toList.map (·.toString) |>.filter (· ≠ ""))

def tidy (ctx : Ctx) (s : String) : String :=
  ctx.short.foldl (fun s (f, sh) => s.replace f sh) s

/-- Natural-number subtraction/division/modulo or integer division inside `e`: these truncate, and
Lean prints them like real arithmetic (red team J, d01: `x ^ (1 / 2)` with a natural-number exponent
`1 / 2 = 0` printed like a square root; d07: `10 ^ (k - 1)`). -/
def truncates (e : Expr) : Bool :=
  (e.find? fun s =>
    ((s.isAppOfArity ``HDiv.hDiv 6 || s.isAppOfArity ``HSub.hSub 6 || s.isAppOfArity ``HMod.hMod 6) &&
      s.getArg! 0 == mkConst ``Nat) ||
    ((s.isAppOfArity ``HDiv.hDiv 6 || s.isAppOfArity ``HMod.hMod 6) && s.getArg! 0 == mkConst ``Int) ||
    s.isConstOf ``Nat.sub || s.isConstOf ``Nat.div || s.isConstOf ``Int.ediv).isSome

/-- Lean notation. Omitted proofs are shown with their statement (red team J, d02 hid the property
of a `Classical.choose` behind `⋯`); terms with truncating arithmetic are printed with numeral types
and flagged. -/
def ppE (ctx : Ctx) (e : Expr) : MetaM String := do
  let tr := truncates e
  let f ← withOptions (fun o => ((((o.setBool `pp.proofs false).setBool `pp.proofs.withType true).setBool
      `pp.numericTypes tr).set `format.width (100000 : Nat))) <| ppExpr e
  let s := tidy ctx (oneLine (toString f))
  return if tr then s ++ " ⚠ TRUNCATING ℕ/ℤ ARITHMETIC" else s

def code (s : String) : String :=
  if s.contains '`' then "``" ++ s ++ "``" else "`" ++ s ++ "`"

def binderNames (n : Name) : MetaM (Array String) := do
  let ci ← getConstInfo n
  forallTelescope ci.type fun xs _ => xs.mapM fun x => return (← x.fvarId!.getUserName).eraseMacroScopes.toString

def fill (tmpl : String) (names vals : Array String) : String :=
  (names.zip vals).foldl (fun s (n, v) => s.replace ("{" ++ n ++ "}") v) tmpl

/-- An atom: a fully applied pinned predicate becomes its phrase, anything else Lean notation. -/
def atom (ctx : Ctx) (e : Expr) : MetaM String := do
  if let some c := e.getAppFn.constName? then
    if ctx.pinned.contains c then
      if let some tmpl := ctx.phrases.find? c then
        let names ← binderNames c
        let args := e.getAppArgs
        if args.size == names.size && (← isProp e) then
          -- each filled slot shows its binder name when the argument is printed differently (run
          -- 2026-11-08T1828Z, blind red team X d05: a phrase listing rate constants `{k₁}, {k₃}, {k₂}`
          -- in the wrong order put the values on the wrong reactions, and the body printed with the
          -- definition uses the binder names): `k₃ := 10000` ties each value to the body's symbol
          let vals ← (args.zip names).mapM fun (a, n) => do
            let s ← ppE ctx a
            return if s == n then code s else code s!"{n} := {s}"
          return fill tmpl names vals
  return code (← ppE ctx e)

partial def conjuncts (e : Expr) : Array Expr :=
  let e := e.consumeMData
  if e.isAppOfArity ``And 2 then conjuncts (e.getArg! 0) ++ conjuncts (e.getArg! 1) else #[e]

/-- A proposition in words. -/
partial def renderProp (ctx : Ctx) (e : Expr) : MetaM String := do
  let e := (← instantiateMVars e).consumeMData
  match e with
  | .forallE n d b bi =>
    if (← isProp d) && !b.hasLooseBVars then
      return s!"if {← renderProp ctx d}, then {← renderProp ctx b}"
    else
      withLocalDecl n bi d fun x => do
        return s!"for every {code s!"{(← x.fvarId!.getUserName).eraseMacroScopes} : {← ppE ctx d}"}, {← renderProp ctx (b.instantiate1 x)}"
  | _ =>
    if e.isAppOfArity ``And 2 then
      let cs ← (conjuncts e).mapM (renderProp ctx)
      return " and ".intercalate (cs.toList.map fun s => s!"({s})")
    if e.isAppOfArity ``Or 2 then
      return s!"either ({← renderProp ctx (e.getArg! 0)}) or ({← renderProp ctx (e.getArg! 1)})"
    if e.isAppOfArity ``Not 1 then
      return s!"it is false that ({← renderProp ctx (e.getArg! 0)})"
    if e.isAppOfArity ``Iff 2 then
      return s!"({← renderProp ctx (e.getArg! 0)}) if and only if ({← renderProp ctx (e.getArg! 1)})"
    if e.isConstOf ``True then return "true (no condition)"
    if e.isConstOf ``False then return "false (a contradiction)"
    for (q, word) in [(``Exists, "there is"), (``ExistsUnique, "there is exactly one")] do
      if e.isAppOfArity q 2 then
        let ty := e.getArg! 0
        match (e.getArg! 1).consumeMData with
        | .lam n _ b bi =>
          return ← withLocalDecl n bi ty fun x => do
            return s!"{word} {code s!"{(← x.fvarId!.getUserName).eraseMacroScopes} : {← ppE ctx ty}"} such that {← renderProp ctx (b.instantiate1 x)}"
        | p =>
          return ← withLocalDecl `x .default ty fun x => do
            return s!"{word} {code s!"x : {← ppE ctx ty}"} such that {← renderProp ctx (mkApp p x)}"
    atom ctx e

/-- Slot names: for each free variable passed directly as an argument of a pinned definition with a
phrase, the binder names of the slots it fills. -/
partial def slots (ctx : Ctx) (e : Expr) (acc : Std.HashMap FVarId (Array String)) :
    MetaM (Std.HashMap FVarId (Array String)) := do
  let mut acc := acc
  if e.isApp then
    if let some c := e.getAppFn.constName? then
      if ctx.pinned.contains c && ctx.phrases.contains c then
        let names ← binderNames c
        let args := e.getAppArgs
        if args.size == names.size then
          for (a, i) in args.zipIdx do
            if a.isFVar then acc := acc.insert a.fvarId! (((acc.get? a.fvarId!).getD #[]).push names[i]!)
  match e with
  | .app f a => do let r ← slots ctx f acc; slots ctx a r
  | .lam _ d b _ | .forallE _ d b _ => do let r ← slots ctx d acc; slots ctx b r
  | .letE _ t v b _ => do let r ← slots ctx t acc; let r ← slots ctx v r; slots ctx b r
  | .mdata _ b => slots ctx b acc
  | _ => return acc

/-- Names the generator chooses for the leading binders (red team J, d04/d05/d08: binder names are
the author's, and `S E P C` or `ΩΛ` fed into pinned slots made a correct claim read wrongly). A data
binder that fills slots of pinned definitions, all with the same slot name, is renamed to it unless
another binder has or wants that name. Returns (index, new name, author's name). -/
def chooseNames (ctx : Ctx) (ty : Expr) : MetaM (Array (Option Name)) :=
  forallTelescope ty fun xs body => do
    let mut acc : Std.HashMap FVarId (Array String) := {}
    for x in xs do acc ← slots ctx (← inferType x) acc
    acc ← slots ctx body acc
    let orig ← xs.mapM fun x => return (← x.fvarId!.getUserName).eraseMacroScopes
    let want : Array (Option Name) ← xs.mapM fun x => do
      if ← isProp (← inferType x) then return none
      match acc.get? x.fvarId! with
      | some ns => if ns.all (· == ns[0]!) then return some (Name.mkSimple ns[0]!) else return none
      | none => return none
    let mut out : Array (Option Name) := #[]
    for (w, i) in want.zipIdx do
      match w with
      | some n =>
        let clash := (want.zipIdx.any fun (w', j) => j != i && w' == some n) ||
          (orig.zipIdx.any fun (o, j) => j != i && o == n && want[j]!.isNone)
        -- keep a decorated form of the slot name (`t₀` for slot `t`, `v₁` for `v`): suffixes of
        -- subscripts, digits or primes only (`ΩΛ` for slot `Ω` is renamed). Red team K, d04 (run
        -- 2026-11-05T1628Z): lowercase-letter suffixes were also kept (for `vc`), and `Ωde` filling
        -- the matter-fraction slot of `IsFlatLCDM` read as a dark-energy fraction; letters now count
        -- as a new name (the author's name is still shown next to the generated one)
        let o := orig[i]!.toString
        let decorated := o.startsWith n.toString && ((o.drop n.toString.length).all fun c =>
          c.isDigit || c == '\'' || ('₀' ≤ c && c ≤ '₉'))
        out := out.push (if clash || decorated then none else some n)
      | none => out := out.push none
    return out

/-- Leading binders: data binders, rendered assumptions, then the conclusion. -/
partial def peel (ctx : Ctx) (ty : Expr) (data hyps : Array String) (names : Array (Option Name) := #[])
    (i : Nat := 0) : MetaM (Array String × Array String × Array String) := do
  match (← instantiateMVars ty).consumeMData with
  | .forallE n d b bi =>
    let new := (names[i]?).getD none
    withLocalDecl (new.getD n) bi d fun x => do
      let nm := (← x.fvarId!.getUserName).eraseMacroScopes
      let b' := b.instantiate1 x
      if bi.isInstImplicit then
        peel ctx b' data (hyps.push s!"(instance) {code (← ppE ctx d)}") names (i + 1)
      else if (← isProp d) then
        peel ctx b' data (hyps.push (← renderProp ctx d)) names (i + 1)
      else
        let note := if new.isSome then s!" (renamed by the generator after the pinned slot it fills; the statement calls it {code n.eraseMacroScopes.toString})" else ""
        peel ctx b' (data.push (code s!"{nm} : {← ppE ctx d}" ++ note)) hyps names (i + 1)
  | c =>
    let cs ← (conjuncts c).mapM (renderProp ctx)
    return (data, hyps, cs)

/-- A definition's meaning, with its own binder names. -/
def explain (ctx : Ctx) (d : Name) : MetaM String := do
  let ci ← getConstInfo d
  let shortD := tidy ctx d.toString
  match ctx.pinned.find? d with
  | some pin =>
    let tmpl := (ctx.phrases.find? d).getD "(no phrase)"
    let pre ← forallTelescope ci.type fun xs _ => do
      let names ← xs.mapM fun x => return (← x.fvarId!.getUserName).eraseMacroScopes.toString
      let head ← ppE ctx (mkAppN (.const d (ci.levelParams.map Level.param)) xs)
      let vals := names.map code
      return s!"- {code head} — **PINNED** (pin theorem {code (tidy ctx pin.toString)}): phrase (hand-written, linted): {fill tmpl names vals}"
    -- the body, printed by Lean (run 2026-11-08T1828Z, blind round W d04: a phrase is author text and
    -- carried a formula, "a′(t)/a(t)", onto `|hubble|`; phrases now contain no formula, rule P1 of
    -- check_claims.py, and every formula a reader sees comes from the definition itself)
    -- certified phrase lines (rule P13 of check_claims.py, run 2026-11-09T1828Z): each reader line of the phrase
    -- that a Checked theorem proves, with that theorem's hypotheses printed by Lean (the conditions under which the
    -- line was proved); full statements in PHRASE_LINES.md
    let certs := (ctx.certs.find? d).getD #[]
    let mut notes : Array String := #[]
    for (line, th) in certs do
      let ty := (← getConstInfo th).type
      let (_, hs, _) ← peel ctx ty #[] #[] (← chooseNames ctx ty)
      let hs := hs.filter (· != "")
      notes := notes.push (if hs.isEmpty then s!"«{line}»" else s!"«{line}» only assuming {"; ".intercalate hs.toList}")
    let certNote := if notes.isEmpty then "" else
      s!". Phrase lines proved in Lean (statements in PHRASE_LINES.md): {", ".intercalate notes.toList}"
    match ci with
    | .defnInfo dv =>
      lambdaTelescope dv.value fun xs body => do
        let head ← ppE ctx (mkAppN (.const d (ci.levelParams.map Level.param)) xs)
        if ← isProp body then
          return s!"{pre}; by definition, means {← renderProp ctx body}{certNote}"
        else
          return s!"{pre}; by definition, {code head} is {code (← ppE ctx body)}{certNote}"
    | _ => return pre ++ certNote
  | none =>
    let kind := (ctx.kinds.find? d).getD "UNCLASSIFIED"
    match ci with
    | .defnInfo dv =>
      lambdaTelescope dv.value fun xs body => do
        let head ← ppE ctx (mkAppN (.const d (ci.levelParams.map Level.param)) xs)
        let sig ← xs.mapM fun x => do return code s!"{(← x.fvarId!.getUserName).eraseMacroScopes} : {← ppE ctx (← inferType x)}"
        let sigTxt := if sig.isEmpty then "" else s!" (for {", ".intercalate sig.toList})"
        -- objects picked by choice: say what they are known to satisfy (red team J, d02: a
        -- `Classical.choose` of an auxiliary theorem showed only `Classical.choose name`)
        let mut extra := ""
        let mut seen : Array Expr := #[]
        let mut todo : Array Expr := #[body]
        while !todo.isEmpty do
          let t := todo.back!
          todo := todo.pop
          if t.isAppOfArity ``Classical.choose 3 && !seen.contains t then
            seen := seen.push t
            let pf := t.getArg! 2
            extra := extra ++ s!"; {code (← ppE ctx t)} is an object chosen without construction, known only to satisfy: {← renderProp ctx (← inferType pf)}"
          match t with
          | .app f a => todo := todo.push f |>.push a
          | .lam _ d b _ | .forallE _ d b _ => todo := todo.push d |>.push b
          | .mdata _ b => todo := todo.push b
          | .letE _ ty v b _ => todo := todo.push ty |>.push v |>.push b
          | .proj _ _ b => todo := todo.push b
          | _ => pure ()
        -- numeric constants in a formula are data nobody compared with a source (red team J, d03:
        -- the gas constant with transposed digits inside a FORMULA)
        if kind != "PRINTED" && (body.find? fun s => s.isAppOfArity ``OfScientific.ofScientific 5).isSome then
          extra := extra ++ " ⚠ contains decimal constants that no check compares with a source"
        -- a blind second formulation (run 2026-11-05T0828Z, `Checked/Trust/Formulations.lean`)
        -- checks the name against the body: say so, with the agreement theorem's name
        let agreeN := (`Checked.Trust.Formulations).str ("agree_" ++ d.componentsRev.head!.toString)
        let sf : Bool := match (← getEnv).find? agreeN with
          | some ai => match ai.type.eq? with
            | some (_, l, _) => l.isConstOf d
            | none => false
          | none => false
        -- a PRINTED transcription with an independent second reading (trust track T3,
        -- `Checked/Trust/Transcriptions*.lean`; run 2026-11-05T1028Z: CLAIMS.md did not say so)
        let readN := (`Checked.Trust.Transcriptions).str ("agree_" ++ d.componentsRev.head!.toString)
        -- run 2026-11-05T2028Z: CLAIMs too (their inline formula or series order, read a second time)
        let sr : Bool := (kind == "PRINTED" || kind == "CLAIM") && match (← getEnv).find? readN with
          | some ai => match ai.type.eq? with
            | some (_, l, _) => l.isConstOf d
            | none => false
          | none => false
        let status := if sf then s!"not pinned; name and body agree with a blind second formulation ({code (tidy ctx agreeN.toString)})"
          else if sr && kind == "CLAIM" then s!"not pinned; the source-dependent data written inline (printed formula, order of the printed series) agree with an independent blind second reading of the source ({code (tidy ctx readN.toString)}); the quantifiers and hypotheses are the program's formalisation"
          else if sr then s!"not pinned; an independent blind second reading of the source agrees with this transcription ({code (tidy ctx readN.toString)}); its name is not checked"
          else "not pinned, so only the formula shown is checked, not its name"
        if ← isProp body then
          return s!"- {code head} — {kind}, {status}{sigTxt}: means {← renderProp ctx body}{extra}"
        else
          return s!"- {code head} — {kind}, {status}{sigTxt}: is defined as {code (← ppE ctx body)}{extra}"
    | .inductInfo iv =>
      let cs ← iv.ctors.mapM fun k => do return code s!"{tidy ctx k.toString} : {← ppE ctx (← getConstInfo k).type}"
      return s!"- {code shortD} — {kind}, not pinned: inductive type with constructors {", ".intercalate cs}"
    | _ => return s!"- {code shortD} — {kind}, not pinned: {code (← ppE ctx ci.type)}"

end Claims

/-! Planted controls of `Claims.closureFaults` (run 2026-11-25T2028Z): a fake headline, a fake blind reading, one
valid closures and six forged ones (run 2026-11-26T0228Z: three more valid, five more forged). The generator fails before writing any page unless the valid one passes and each
forged one is rejected for the reason it plants. -/
namespace ClosureControls
def SecondReading.reading : Prop := ∀ m : ℕ, m + 0 = m
def SecondReading.weak : Prop := True
def other : Prop := ∀ m : ℕ, m + 0 = m
theorem head : ∀ n : ℕ, n + 0 = n := fun _ => rfl
theorem helper : ∀ n : ℕ, n + 0 = n := fun _ => rfl
set_option linter.defProp false in
def stored : ∀ n : ℕ, n + 0 = n := fun _ => rfl
/-- valid: holds by unfolding -/
theorem good : SecondReading.reading ↔ ∀ n : ℕ, n + 0 = n := Iff.rfl
/-- forged: a weak reading, the equivalence proved because both sides are proved by the program -/
theorem uses_head : SecondReading.weak ↔ ∀ n : ℕ, n + 0 = n := iff_of_true trivial head
/-- forged: as above through a helper theorem of the program -/
theorem uses_helper : SecondReading.weak ↔ ∀ n : ℕ, n + 0 = n := iff_of_true trivial helper
/-- forged: as above through a proof stored as a definition -/
theorem uses_stored : SecondReading.weak ↔ ∀ n : ℕ, n + 0 = n := iff_of_true trivial stored
/-- forged: a weak reading, both sides re-proved without any theorem of the program -/
theorem reproves : SecondReading.weak ↔ ∀ n : ℕ, n + 0 = n := iff_of_true trivial (fun n => Nat.add_zero n)
/-- valid: a bridge by rewriting under the binder -/
theorem good_congr : SecondReading.reading ↔ ∀ n : ℕ, n + 0 = n := forall_congr' fun _ => Iff.rfl
/-- forged: the reading is not a blind reader's definition -/
theorem not_reading : other ↔ ∀ n : ℕ, n + 0 = n := Iff.rfl
/-- forged: neither side is the headline's statement -/
theorem wrong_side : SecondReading.reading ↔ ∀ n : ℕ, 0 + n = n := by
  simp only [SecondReading.reading, Nat.add_zero, Nat.zero_add]
/-! Run 2026-11-26T0228Z: controls of the followed kinds (auxiliary proofs of definitions, equation lemmas, the
closure's own helpers). The three valid ones were rejected by the first version of the rule. -/
def SecondReading.reading10 : Prop := ∀ y : ℝ, y * 10 = 10 * y
theorem head10 : ∀ x : ℝ, x * 10 = 10 * x := fun x => mul_comm x 10
/-- valid: the reading's numeral 10 makes Lean abstract a proof of `(9 + 1).AtLeastTwo` out of its body -/
theorem good_numeral : SecondReading.reading10 ↔ ∀ x : ℝ, x * 10 = 10 * x := Iff.rfl
/-- valid: unfolding by `rw`, through the equation lemma of the reading -/
theorem good_eqn : SecondReading.reading ↔ ∀ n : ℕ, n + 0 = n := by rw [SecondReading.reading]
theorem good_helper.flip {P Q : Prop} (h : P ↔ Q) : Q ↔ P := h.symm
/-- valid: a Mathlib-only helper named under the closure -/
theorem good_helper : SecondReading.reading ↔ ∀ n : ℕ, n + 0 = n := good_helper.flip Iff.rfl
theorem helper_side.side : ∀ n : ℕ, n + 0 = n := fun n => Nat.add_zero n
/-- forged: a weak reading, the headline re-proved in a helper of the closure -/
theorem helper_side : SecondReading.weak ↔ ∀ n : ℕ, n + 0 = n := iff_of_true trivial helper_side.side
theorem helper_both.both : SecondReading.weak ↔ ∀ n : ℕ, n + 0 = n := iff_of_true trivial (fun n => Nat.add_zero n)
/-- forged: the whole forged equivalence moved into a helper of the closure -/
theorem helper_both : SecondReading.weak ↔ ∀ n : ℕ, n + 0 = n := helper_both.both
theorem helper_prog.via : ∀ n : ℕ, n + 0 = n := head
/-- forged: a helper of the closure that uses the program's headline -/
theorem helper_prog : SecondReading.weak ↔ ∀ n : ℕ, n + 0 = n := iff_of_true trivial helper_prog.via
theorem fake._proof_1 : ∀ n : ℕ, n + 0 = n := head
/-- forged: a theorem of the program given an auxiliary's name -/
theorem aux_named : SecondReading.weak ↔ ∀ n : ℕ, n + 0 = n := iff_of_true trivial fake._proof_1
theorem Deep.strong : (∀ n : ℕ, n + 0 = n) ∧ True := ⟨head, trivial⟩
end ClosureControls
/-- forged (red team BA): a closure theorem named like the program's root namespace, so that every theorem of the
program is a name below it -/
theorem ClosureControls : ClosureControls.SecondReading.weak ↔ ∀ n : ℕ, n + 0 = n :=
  ⟨fun _ => ClosureControls.Deep.strong.1, fun _ => trivial⟩

open Claims in
run_cmd do
  let env ← getEnv
  let isProg := fun (c : Name) => (`ClosureControls).isPrefixOf c
  let isRd := fun (c : Name) => (`ClosureControls.SecondReading).isPrefixOf c
  let cases : List (Name × Option String) := [
    (`ClosureControls.good_eqn, none),
    (`ClosureControls.good_helper, none),
    (`ClosureControls.helper_side, some "contains a proof of one side"),
    (`ClosureControls.helper_both, some "contains a proof of one side"),
    (`ClosureControls.helper_prog, some "theorem ClosureControls.head"),
    (`ClosureControls.aux_named, some "theorem ClosureControls.head"),
    (`ClosureControls, some "theorem ClosureControls.Deep.strong"),
    (`ClosureControls.good, none),
    (`ClosureControls.good_congr, none),
    (`ClosureControls.reproves, some "contains a proof of one side"),
    (`ClosureControls.uses_head, some "theorem ClosureControls.head"),
    (`ClosureControls.uses_helper, some "theorem ClosureControls.helper"),
    (`ClosureControls.uses_stored, some "theorem ClosureControls.stored"),
    (`ClosureControls.not_reading, some "is not a definition of a"),
    (`ClosureControls.wrong_side, some "neither side")]
  for (t, want) in cases do
    let faults ← liftTermElabM <| closureFaults env isProg isRd `ClosureControls.head t
    match want with
    | none => unless faults.isEmpty do throwError m!"closure control {t}: valid closure rejected: {faults.toList}"
    | some w => unless faults.any (fun f => (f.splitOn w).length > 1) do
        throwError m!"closure control {t}: forged closure not rejected for `{w}`: {faults.toList}"
  -- a headline with a numeral (run 2026-11-26T0228Z)
  let faults ← liftTermElabM <| closureFaults env isProg isRd `ClosureControls.head10 `ClosureControls.good_numeral
  unless faults.isEmpty do throwError m!"closure control good_numeral: valid closure rejected: {faults.toList}"

/-! Planted controls of `Claims.paramClosureFaults` (run 2026-11-26T0828Z, `runs/2026-11-26T0828Z/t5/RESULTS_PARAM.md`):
three valid closures and ten forged ones. The generator fails before writing any page unless each valid one is accepted
and each forged one is rejected for the reason it plants. -/
namespace ParamControls
theorem head : (2 : ℝ) < 3 := by norm_num
theorem head2 : (3 / 2 : ℝ) < 2 := by norm_num
theorem headN : ∀ x : ℝ, 0 ≤ x ^ 2 ∨ x = 2 := fun x => Or.inl (sq_nonneg x)
theorem headZ : ∀ x : ℝ, x * 0 = 0 := fun x => by ring
namespace SecondReading
def r : Prop := (3 : ℝ) > 2
def r2 : Prop := (1.5 : ℝ) < 2
def rN : Prop := True
def rC : Prop := ((2 : ℝ) = 2 ∧ (3 : ℝ) = 3) ∨ (2 : ℝ) < 3
def rD : Prop := ((2 : ℝ) = 2 ∧ (3 : ℝ) = 3) ∨ (3 : ℝ) > 2
def rZ : Prop := True
end SecondReading
def other : Prop := (3 : ℝ) > 2
/-- valid -/
theorem good : ∀ a b : ℝ, b > a ↔ a < b := fun _ _ => Iff.rfl
theorem good.bite : ¬ ∀ a b : ℝ, a < b := fun h => lt_irrefl _ (h 0 0)
/-- valid: variables in the other order -/
theorem good_order : ∀ b a : ℝ, b > a ↔ a < b := fun _ _ => Iff.rfl
theorem good_order.bite : ¬ ∀ b a : ℝ, a < b := fun h => lt_irrefl _ (h 0 0)
/-- valid: the reading writes 1.5 where the headline writes 3 / 2 -/
theorem good_norm : ∀ a b : ℝ, a < b ↔ a < b := fun _ _ => Iff.rfl
theorem good_norm.bite : ¬ ∀ a b : ℝ, a < b := fun h => lt_irrefl _ (h 0 0)
/-- forged: the test-AZ shape, not parametric -/
theorem old_style : SecondReading.r ↔ (2 : ℝ) < 3 := iff_of_true (by unfold SecondReading.r; norm_num) head
theorem old_style.bite : ¬ ∀ a b : ℝ, a < b := fun h => lt_irrefl _ (h 0 0)
/-- forged: variables quantified but the literals kept -/
theorem kept : ∀ a b : ℝ, (3 : ℝ) > 2 ↔ (2 : ℝ) < 3 := fun _ _ => iff_of_true (by norm_num) (by norm_num)
theorem kept.bite : ¬ ∀ a b : ℝ, a < b := fun h => lt_irrefl _ (h 0 0)
/-- forged: one literal varied, one kept -/
theorem one_var : ∀ a b : ℝ, b > 2 ↔ 2 < b := fun _ _ => Iff.rfl
theorem one_var.bite : ¬ ∀ a b : ℝ, a < b := fun h => lt_irrefl _ (h 0 0)
/-- forged: a literal that does not bite, with no bite theorem -/
theorem nobite : ∀ c : ℝ, SecondReading.rN ↔ ∀ x : ℝ, 0 ≤ x ^ 2 ∨ x = c :=
  fun _ => iff_of_true trivial fun x => Or.inl (sq_nonneg x)
/-- forged: a literal that does not bite, with a bite theorem of another statement -/
theorem nobite2 : ∀ c : ℝ, SecondReading.rN ↔ ∀ x : ℝ, 0 ≤ x ^ 2 ∨ x = c :=
  fun _ => iff_of_true trivial fun x => Or.inl (sq_nonneg x)
theorem nobite2.bite : ¬ ∀ c : ℝ, c * 0 = 1 := fun h => by have := h 0; norm_num at this
/-- forged: a reading that holds the headline behind a case split on its literals -/
theorem case_split : ∀ a b : ℝ, ((a = 2 ∧ b = 3) ∨ a < b) ↔ a < b := fun a b =>
  ⟨fun h => h.elim (fun ⟨ha, hb⟩ => by subst ha hb; norm_num) id, Or.inr⟩
theorem case_split.bite : ¬ ∀ a b : ℝ, a < b := fun h => lt_irrefl _ (h 0 0)
/-- forged: the left side is not the reading -/
theorem wrong_rd : ∀ a b : ℝ, a < b ↔ a < b := fun _ _ => Iff.rfl
theorem wrong_rd.bite : ¬ ∀ a b : ℝ, a < b := fun h => lt_irrefl _ (h 0 0)
/-- forged: the reading is not a blind reader's definition -/
theorem not_rd : ∀ a b : ℝ, b > a ↔ a < b := fun _ _ => Iff.rfl
theorem not_rd.bite : ¬ ∀ a b : ℝ, a < b := fun h => lt_irrefl _ (h 0 0)
/-- forged: a headline with no literal to vary -/
theorem nolit : SecondReading.rZ ↔ ∀ x : ℝ, x * 0 = 0 := iff_of_true trivial headZ
/-- forged: the case split with the headline restated (`b > a` for `a < b`), accepted by the first version -/
theorem case_split2 : ∀ a b : ℝ, ((a = 2 ∧ b = 3) ∨ b > a) ↔ a < b := fun a b =>
  ⟨fun h => h.elim (fun ⟨ha, hb⟩ => by subst ha hb; norm_num) id, Or.inr⟩
theorem case_split2.bite : ¬ ∀ a b : ℝ, a < b := fun h => lt_irrefl _ (h 0 0)
end ParamControls

open Claims in
run_cmd do
  let env ← getEnv
  let isRd := fun (c : Name) => (`ParamControls.SecondReading).isPrefixOf c
  for (h, t, rn, w) in [(`ParamControls.head, `ParamControls.good, `ParamControls.SecondReading.r, none),
      (`ParamControls.head, `ParamControls.good_order, `ParamControls.SecondReading.r, none),
      (`ParamControls.head2, `ParamControls.good_norm, `ParamControls.SecondReading.r2, none),
      (`ParamControls.head, `ParamControls.old_style, `ParamControls.SecondReading.r, some "must quantify"),
      (`ParamControls.head, `ParamControls.kept, `ParamControls.SecondReading.r, some "right side"),
      (`ParamControls.head, `ParamControls.one_var, `ParamControls.SecondReading.r, some "right side"),
      (`ParamControls.headN, `ParamControls.nobite, `ParamControls.SecondReading.rN, some "no theorem"),
      (`ParamControls.headN, `ParamControls.nobite2, `ParamControls.SecondReading.rN, some "does not state `¬"),
      (`ParamControls.head, `ParamControls.case_split, `ParamControls.SecondReading.rC, some "contains the headline"),
      (`ParamControls.head, `ParamControls.wrong_rd, `ParamControls.SecondReading.r, some "is not the reading"),
      (`ParamControls.head, `ParamControls.not_rd, `ParamControls.other, some "is not a `def"),
      (`ParamControls.headZ, `ParamControls.nolit, `ParamControls.SecondReading.rZ, some "no real literal"),
      (`ParamControls.head, `ParamControls.case_split2, `ParamControls.SecondReading.rD, some "keeps a numeral")] do
    let faults ← liftTermElabM <| paramClosureFaults env isRd h t rn
    match w with
    | none => unless faults.isEmpty do throwError m!"parametric closure control {t}: valid closure rejected: {faults.toList}"
    | some s => unless faults.any (fun f => (f.splitOn s).length > 1) do
        throwError m!"parametric closure control {t}: forged closure not rejected for `{s}`: {faults.toList}"

open Claims in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let cands : Array Name := env.constants.map₁.fold (init := #[]) fun acc n _ =>
    if isCheckedConst env n && !(privateToUserName n).isInternal then acc.push n else acc
  let mut errors : Array String := #[]
  let mut pinned : NameMap Name := {}
  for l in ← readLines "scripts/trust/pins.txt" do
    match l.splitOn " " |>.filter (· ≠ "") with
    | [d, t] =>
      match resolve cands d, resolve cands t with
      | .ok dn, .ok tn => pinned := pinned.insert dn tn
      | .error e, _ | _, .error e => errors := errors.push e
    | _ => errors := errors.push s!"bad pins line: {l}"
  let mut kinds : NameMap String := {}
  for l in ← readLines "scripts/trust/def_kinds.txt" do
    match l.splitOn " " |>.filter (· ≠ "") with
    | [d, k] => if let .ok dn := resolve cands d then kinds := kinds.insert dn k
    | _ => pure ()
  let mut phrases : NameMap String := {}
  for l in ← readLines "scripts/trust/phrases.txt" do
    match l.splitOn " | " with
    | d :: rest =>
      match resolve cands d.trimAscii.copy with
      | .ok dn =>
        let tmpl := " | ".intercalate rest
        unless pinned.contains dn do errors := errors.push s!"phrases.txt: {dn} is not pinned (phrases are for pinned definitions only)"
        let names ← liftTermElabM <| binderNames dn
        -- every placeholder must be a binder name of the definition
        let holes := ((tmpl.splitOn "{").drop 1).map fun s => (s.splitOn "}").head!
        for h in holes do
          unless names.contains h do errors := errors.push s!"phrases.txt: placeholder \{{h}} of {dn} is not one of its binders {names.toList}"
        phrases := phrases.insert dn tmpl
      | .error e => errors := errors.push s!"phrases.txt: {e}"
    | [] => pure ()
  -- certified phrase lines (rule P13 of check_claims.py, run 2026-11-09T1828Z)
  let mut certs : NameMap (Array (String × Name)) := {}
  let mut certList : Array (Name × String × String × Name) := #[]
  for l in ← readLines "scripts/trust/phrase_certs.txt" do
    -- every non-comment line must parse (adversary AE d01: a line Lean skipped silently while Python counted it)
    unless l.startsWith "CERT | " do
      errors := errors.push s!"phrase_certs.txt: line is neither a comment nor a CERT line: {l}"
      continue
    match (l.splitOn " | ").map (·.trimAscii.copy) with
    | [_, kind, d, line, th] =>
      match resolve cands d, resolve cands th with
      | .ok dn, .ok tn =>
        let some tc := env.find? tn | errors := errors.push s!"phrase_certs.txt: {th} not found"
        match tc with
        | .thmInfo _ =>
          unless tc.type.getUsedConstants.contains dn do
            errors := errors.push s!"phrase_certs.txt: the statement of {tn} does not use {dn} (P13: a certificate is a theorem about the definition)"
          -- adversary AE d02-d04: the theorem's docstring quotes the line it certifies; the definition occurs in
          -- the conclusion (not only in a hypothesis); the conclusion has no implication and no data binder is a
          -- subtype, so every condition is a printed hypothesis
          let doc := oneLine ((← findDocString? env tn).getD "")
          unless (doc.splitOn s!"\"{line}\"").length > 1 do
            errors := errors.push s!"phrase_certs.txt: the docstring of {tn} does not quote the line \"{line}\" (P13)"
          let shape ← liftTermElabM <| (forallTelescope tc.type fun xs body => do
            let mut bad : Array String := #[]
            for x in xs do
              let xt ← inferType x
              if xt.getAppFn.isConstOf ``Subtype then bad := bad.push "a data binder is a subtype"
            let mut hasImp := false
            let mut stack : Array Expr := #[body]
            while !stack.isEmpty do
              let e := stack.back!
              stack := stack.pop
              match e with
              | .forallE _ d b _ =>
                -- a non-dependent arrow is an implication, unless it is a negation (`P → False`)
                if !b.hasLooseBVar 0 && !b.isConstOf ``False then hasImp := true
                stack := (stack.push d).push b
              | .app f a => stack := (stack.push f).push a
              | .lam _ d b _ => stack := (stack.push d).push b
              | .mdata _ b => stack := stack.push b
              | _ => pure ()
            if hasImp then bad := bad.push "the conclusion contains an implication"
            -- a value definition must occur in the conclusion; a predicate may instead occur in a hypothesis (the
            -- line then states a consequence of the predicate)
            let isPred ← forallTelescope (← getConstInfo dn).type fun _ b => return b.isProp
            let inHyp ← xs.anyM fun x => do return (← inferType x).getUsedConstants.contains dn
            unless body.getUsedConstants.contains dn || (isPred && inHyp) do
              bad := bad.push s!"the conclusion does not use {dn}"
            return bad : MetaM (Array String))
          for b in shape do
            errors := errors.push s!"phrase_certs.txt: {tn}: {b} (P13: every condition must be a printed hypothesis)"
          unless phrases.contains dn do
            errors := errors.push s!"phrase_certs.txt: {dn} has no phrase"
          certs := certs.insert dn (((certs.find? dn).getD #[]).push (line, tn))
          certList := certList.push (dn, kind, line, tn)
        | _ => errors := errors.push s!"phrase_certs.txt: {tn} is not a theorem"
      | .error e, _ | _, .error e => errors := errors.push s!"phrase_certs.txt: {e}"
    | _ => errors := errors.push s!"phrase_certs.txt: malformed line {l}"
  let stop : NameSet := pinned.foldl (init := {}) fun s n _ => s.insert n
  let heads ← readLines "scripts/trust/headlines.txt"
  let mut hs : Array Name := #[]
  for h in heads do
    match resolve cands h with
    | .ok hn => hs := hs.push hn
    | .error e => errors := errors.push e
  -- every program definition reached by some headline, for the display names
  let mut reachedAll : NameSet := {}
  for hn in hs do
    for d in (deps env stop (env.find? hn).get!.type {}).toList do
      if reportable env d then reachedAll := reachedAll.insert d
  -- lookalike names (red team J, d07: `RoundsTo'` with a looser tolerance read as `RoundsTo`): two
  -- reached definitions whose last names agree after removing primes are an error
  let strip := fun (n : Name) => n.componentsRev.head!.toString.replace "'" ""
  for d in reachedAll.toList do
    for e in reachedAll.toList do
      if d.toString < e.toString && strip d == strip e && d.componentsRev.head! != e.componentsRev.head! then
        errors := errors.push s!"lookalike definitions {d} and {e} (names equal up to primes): rename one"
  let shown := reachedAll.toList ++ hs.toList ++ pinned.toList.map (·.2)
  -- display name: the shortest dotted suffix that no other shown constant shares
  let suffix := fun (n : Name) (k : Nat) => ".".intercalate ((n.components.map toString).drop (n.components.length - k))
  let short : Array (String × String) := (shown.map fun n =>
    let k := (List.range n.components.length).map (· + 1) |>.find? (fun k =>
      !(shown.any fun m => m != n && (m.toString == suffix n k || m.toString.endsWith ("." ++ suffix n k))))
    (n.toString, suffix n (k.getD n.components.length))).toArray.qsort (fun a b => a.1.length > b.1.length)
  let ctx : Ctx := { pinned, kinds, phrases, certs, short }
  -- generated fidelity record (run 2026-11-18T0828Z, part 3; `runs/2026-11-18T0828Z/t5/`): blind readers of run
  -- 2026-11-18T0228Z kept the generated kernel status and still declined to cite a valid headline when a
  -- hand-written line claimed a *fidelity* flaw ("it does not say what the source says"): the Status line
  -- answered only whether Lean proved the statement. The record below states, from Lean and the committed
  -- registries CI checks, what has been machine-checked about the statement's meaning: non-vacuity witness
  -- (same rule as StatementDeps.lean), hypothesis necessity counts (same obligations and the same exact-type
  -- match as StatementDeps.lean's `.lake/necessity.tsv`), blind literal readings (`literal_readings.txt`,
  -- matched by check_literals.py) and grandfathered unread literals (`literal_baseline.txt`), the freeze
  -- (`frozen.txt`, check_relock.py).
  let mut thmByHash : Std.HashMap UInt64 (Array (Name × Expr)) := {}
  for (n, ci) in env.constants.map₁.toList do
    if isCheckedConst env n && !(privateToUserName n).isInternal then
      if let .thmInfo t := ci then
        thmByHash := thmByHash.insert t.type.hash ((thmByHash.getD t.type.hash #[]).push (n, t.type))
  let findThm := fun (e : Expr) (avoid : Name) =>
    ((thmByHash.getD e.hash #[]).filter fun (n, t) => n != avoid && t == e).map (·.1)
  let mut litReaders : NameMap (Array Name) := {}
  let mut litSources : NameMap (Array String) := {}
  for l in ← readLines "scripts/trust/literal_readings.txt" do
    let toks := (l.splitOn " ").filter (· != "")
    match toks with
    | h :: rest =>
      match resolve cands h with
      | .ok hn =>
        for t in rest do
          if t.startsWith "source=" then
            for s in ((t.drop 7).copy.splitOn ",") do
              unless ((litSources.find? hn).getD #[]).contains s do
                litSources := litSources.insert hn (((litSources.find? hn).getD #[]).push s)
          else
            let rn := t.toName
            if (env.find? rn).isNone then
              errors := errors.push s!"literal_readings.txt: reader constant {t} does not resolve"
            unless ((litReaders.find? hn).getD #[]).contains rn do
              litReaders := litReaders.insert hn (((litReaders.find? hn).getD #[]).push rn)
      | .error e => errors := errors.push s!"literal_readings.txt: {e}"
    | [] => pure ()
  let mut litBase : NameMap Nat := {}
  for l in ← readLines "scripts/trust/literal_baseline.txt" do
    match l.splitOn " | " with
    | h :: lits :: _ =>
      unless h.startsWith "hidden:" do
        match resolve cands h.trimAscii.copy with
        | .ok hn => litBase := litBase.insert hn (((lits.splitOn " ").filter (· != "")).length)
        | .error e => errors := errors.push s!"literal_baseline.txt: {e}"
    | _ => errors := errors.push s!"literal_baseline.txt: malformed line {l}"
  -- open fidelity objections (run 2026-11-18T0828Z, `scripts/trust/objections.txt`): printed in the Status line
  let mut objections : NameMap (Array String) := {}
  -- closed entries (run 2026-11-25T2028Z, test AZ): fifth field `closed by <theorem>`, checked by `closureFaults`
  let mut closedObjs : NameMap (Array String) := {}
  let isRd := fun (c : Name) => match env.getModuleIdxFor? c with
    | some idx =>
      let m := env.header.moduleNames[idx.toNat]!
      (`Checked.Trust).isPrefixOf m && m.componentsRev.head!.toString.startsWith "SecondReading"
    | none => false
  for l in ← readLines "scripts/trust/objections.txt" do
    match (l.splitOn " | ").map (·.trimAscii.copy) with
    | [h, run, path, summary, clos] =>
      match resolve hs h, (if clos.startsWith "closed by " then some ((clos.drop 10).toString) else none) with
      | .ok hn, some tn =>
        unless (← System.FilePath.pathExists path) do
          errors := errors.push s!"objections.txt: {path} does not exist"
        if summary.isEmpty then errors := errors.push s!"objections.txt: empty summary in {l}"
        -- run 2026-11-26T0828Z: `closed by <theorem> reading <definition>`, checked by the parametric rule
        let (tnS, rnS) := match tn.splitOn " reading " with
          | [a, b] => (a.trimAscii.copy, some b.trimAscii.copy)
          | _ => (tn.trimAscii.copy, none)
        match resolve cands tnS, rnS.map (resolve cands ·) with
        | .ok t, some (.ok rn) =>
          let faults ← liftTermElabM <| paramClosureFaults env isRd hn t rn
          for f in faults do errors := errors.push s!"objections.txt: closure of the entry on {hn}: {f}"
          -- Suspended (run 2026-11-26T0228Z, red team BA round 2, runs/2026-11-26T0228Z/t5/RESULTS_BENCH.md): a
          -- 45-line metaprogram inlined the program's own proof of a headline (no theorem constant left) and threaded
          -- the reading's proof through it (no closed proof of a side left); `closureFaults` accepted `True ↔ H`.
          -- No closure is accepted until the rule decides by more than constant names (planned: a closure parametric
          -- in the headline's literals). `closureFaults` and its controls stay, as the rule under repair.
          -- Still suspended (run 2026-11-26T0828Z, red team BB, runs/2026-11-26T0828Z/t5/RESULTS_PARAM.md): the
          -- parametric rule rejects both forgeries of red team BA and 4/4 honest bench closures pass it, but a reading
          -- that restates the headline behind a disjunct true at a re-spelt literal (`c ≥ √(3.321992119 ^ 2) ∨ …`)
          -- passes; a statement-shape rule cannot see a re-spelling, so closures wait for a check on the reading.
          -- Abandoned (run 2026-11-26T1428Z, runs/2026-11-26T1428Z/t5/RESULTS_COPY.md): the reading need not re-spell
          -- anything. A copy of the headline's own statement, offered as the reading, passes this rule (an honest
          -- agreeing reading may be the same term, so `X = H[c]` must be allowed) and its route passes
          -- check_blind_route.py, check_brief_leak.py and check_provenance.py (brief, reading, copy in three commits);
          -- with a planted unfaithful headline (3.5 for the source's 3.321992119) the copy closes the objection the
          -- honest reading cannot. What separates the two is who wrote the reading, which no check on the repository
          -- sees. A closure field stays a blocking error for good; an entry leaves only by re-freeze or withdrawal.
          errors := errors.push s!"objections.txt: closure of the entry on {hn}: closures are abandoned (a copy of the headline's statement passes as the reading through every check; runs/2026-11-26T1428Z/t5/RESULTS_COPY.md): the entry stays open until the headline is re-frozen or withdrawn"
          closedObjs := closedObjs.insert hn (((closedObjs.find? hn).getD #[]).push
            s!"raised in run {run}, its text written in {code path} (author prose, not printed on this page); closed by the Checked theorem {code t.toString}: a blind reader's statement of the source claim, with the headline's literals made variables, is equivalent to the headline at every value of them, and the literals bite (checked by the generator of this page)")
        | .ok _, none => errors := errors.push s!"objections.txt: fifth field must be `closed by <theorem> reading <definition>`: {l}"
        | .error e, _ => errors := errors.push s!"objections.txt: closure theorem: {e}"
        | _, some (.error e) => errors := errors.push s!"objections.txt: closure reading: {e}"
      | .error e, _ => errors := errors.push s!"objections.txt: {e}"
      | _, none => errors := errors.push s!"objections.txt: fifth field must be `closed by <theorem>`: {l}"
    | [h, run, path, summary] =>
      -- resolved among the registered headlines only (a suffix may also name a witness theorem, e.g. in `Checked.Trust.NV`)
      match resolve hs h with
      | .ok hn =>
        unless (← System.FilePath.pathExists path) do
          errors := errors.push s!"objections.txt: {path} does not exist"
        -- run 2026-11-21T1428Z (blind red team AV, 5/5 accepted): the summary was printed here verbatim, the one piece
        -- of author prose on a page that says it has none, and every defect of the round used it (a 'verdict STANDS,
        -- objection closed' summary, readings the record denies, counts the same line contradicts). An entry now
        -- lowers trust and never raises it: the page shows that an objection is on record and where its text is.
        if summary.isEmpty then errors := errors.push s!"objections.txt: empty summary in {l}"
        objections := objections.insert hn (((objections.find? hn).getD #[]).push
          s!"raised in run {run}, its text written in {code path} (author prose, not printed on this page)")
      | .error e => errors := errors.push s!"objections.txt: {e}"
    | _ => errors := errors.push s!"objections.txt: malformed line {l}"
  let frozenNames : NameSet := (← readLines "scripts/trust/frozen.txt").foldl (init := {}) fun s l =>
    match l.splitOn " " with
    | n :: _ => s.insert n.toName
    | [] => s
  let mut out : Array String := #[
    "# CLAIMS (generated by `scripts/trust/Claims.lean`; do not edit by hand)", "",
    "What each headline theorem claims, **generated mechanically from its Lean statement** (run",
    "2026-11-04T2228Z). The logical structure (for every, assuming, then, and, or, it is false that,",
    "there is) is spelled out by the generator; formulas are printed verbatim by Lean in code spans;",
    "the only hand-written words are the phrases of pinned definitions (`scripts/trust/phrases.txt`,",
    "frozen and linted in CI); since run 2026-11-08T1828Z (blind round W, d04) phrases contain no",
    "formula (rule P1), so every formula in a claim is printed by Lean. Every program definition a",
    "claim uses is listed under it: pinned ones with their phrase AND their definition printed from",
    "Lean, all others with their full definition. The author's docstring follows,",
    "labelled as a paraphrase: **where the paraphrase and the generated claim differ, the generated",
    "claim is what was proved.** CI fails if this file differs from the generator's output.", "",
    "**Status** (run 2026-11-18T0228Z): every headline on this page carries a generated Status line",
    "(its `Checked` module and the axioms Lean computes for it). A headline listed here is proved; a",
    "withdrawn headline is removed from `Checked` and from this page. No hand-written text (a",
    "paraphrase, `STATE.md`, a run record) can withdraw, suspend or qualify a headline listed here.", "",
    "**Fidelity record** (run 2026-11-18T0828Z): the Status line also lists, generated from Lean and the",
    "registries CI checks, what has been machine-checked about the statement's meaning: a non-vacuity witness,",
    "how many hypotheses are shown needed or redundant, blind second readings of its literals, and its freeze.",
    "None of these proves that a statement matches its source; they are the record a fidelity objection meets.",
    "**The record is printed in two parts** (run 2026-11-26T2028Z): **(A)** what the kernel re-derives from the",
    "statement itself (the non-vacuity obligation and each hypothesis's necessity obligation are computed from the",
    "statement by `Checked.Trust`, and a Checked theorem meets them), which holds whoever wrote the statement, the",
    "witnesses and the proofs; and **(B)** what rests on who wrote a statement (objection entries, blind readings,",
    "the specifications that pin definitions, second readings of definitions), which CI checks by route only.",
    "Part A shows the statement is not vacuous and which hypotheses matter; it does not show that the statement",
    "says what its source says. Part B is the only evidence of that, and it is evidence only as far as its writers",
    "were independent of the authors, which no check on this repository can see (THE RESULT part 4, `validation/`).",
    "SPLIT_TOTALS",
    "**What CI checks about a blind second reading is its route, not that its reader was blind:** its brief was",
    "committed before it and holds none of its numbers, and it was committed alone before its copy in `Checked`;",
    "a reading the authors wrote themselves, even a copy of the headline's own statement, passes the same checks",
    "(run 2026-11-26T1428Z).",
    "The record opens with the headline's open fidelity objections from `scripts/trust/objections.txt`, where every",
    "objection to the meaning of a listed headline is entered when it is first written anywhere (since run",
    "2026-11-18T0828Z): an objection that is not shown there has not been recorded as one. An objection's own words",
    "are author prose and are not printed: the record shows that it is open and where it is written. An objection",
    "leaves the record only when its headline is re-frozen (its claim changes) or withdrawn. No entry, reading or",
    "theorem marks an objection settled: closure by a Lean theorem that a second reading of the source is equivalent",
    "to the headline was tested and abandoned, because a copy of the headline's statement passes as such a reading",
    "(runs 2026-11-26T0228Z, 0828Z and 1428Z); the generator of this page fails on any closure field.", "",
    "Notation (Lean/Mathlib, printed as is): `Set.Icc a b` = [a, b]; `Set.Ioo a b` = (a, b);",
    "`√x` = square root; `Real.log` = natural logarithm; `Real.logb b x` = log base b; `deriv f x` =",
    "derivative; `iteratedDeriv n f x` = n-th derivative; `HasDerivAt f f' x` = f has derivative f' at",
    "x; `HasDerivWithinAt f f' s x` = derivative within the set s; `∫ x in a..b, f x` = integral from",
    "a to b; `∀ᶠ t in 𝓝 t₀, P t` = P holds on some neighbourhood of t₀; `f =o[𝓝 x] g` = f is little-o",
    "of g as the argument tends to x; `RoundsTo x d k` = x rounds to the decimal d at k places;",
    "`ContDiffAt ℝ n f x` = f is n times continuously differentiable at x; `87e-3` = 87·10⁻³ = 0.087;",
    "`nhds x` = `𝓝 x`; `deriv^[n] f` = n-th derivative of f.", "",
    "Mathlib's functions are total (run 2026-11-06T2228Z, blind red team P d05): `√x` = 0 for x < 0;",
    "`x / 0` = 0 and `0⁻¹` = 0; `Real.log x` = log |x| for x ≠ 0 and `Real.log 0` = 0; `deriv f x` = 0",
    "where f is not differentiable; an integral of a non-integrable function is 0. A claim that holds only",
    "because of one of these conventions says nothing about the mathematics outside the usual domain.", ""]
  let mut nDone := 0
  let shapes : Std.HashMap String String ← do
    let p : System.FilePath := ".lake/necessity_shape.tsv"
    unless ← p.pathExists do
      throwError "Claims.lean: .lake/necessity_shape.tsv is missing: run scripts/trust/StatementDeps.lean first"
    let ls ← readLines p
    pure <| ls.foldl (init := {}) fun m l => match l.splitOn "\t" with
      | [n, v] => m.insert n v
      | _ => m
  -- totals of the two-part record (run 2026-11-26T2028Z)
  let mut nAComplete := 0
  let mut totNum := 0
  let mut totNeed := 0
  let mut totRed := 0
  let mut totData := 0
  let mut totOpen := 0
  let mut totPin := 0
  let mut totSec := 0
  let mut totBare := 0
  let mut nWithRdr := 0
  let mut nWithBase := 0
  let mut nWithObj := 0
  -- reader page CLAIMS_READER.md (run 2026-11-18T0828Z, rule 2 of `runs/2026-11-18T0828Z/t5/reader_brief.md`): this
  -- page without the author paraphrase blocks; `hdrEnd` = end of the header above, `paraSpans` = paraphrase blocks
  let hdrEnd := out.size
  let mut paraSpans : Array (Nat × Nat) := #[]
  for hn in hs do
    let ci := (env.find? hn).get!
    let doc := (← findDocString? env hn).getD ""
    let reached := (deps env stop ci.type {}).toList.filter (reportable env) |>.toArray.qsort
      (fun a b => tidy ctx a.toString < tidy ctx b.toString)
    for d in reached do
      if pinned.contains d && !phrases.contains d then
        errors := errors.push s!"{hn} reaches the pinned {d}, which has no phrase in scripts/trust/phrases.txt"
    let (data, hyps, concl) ← liftTermElabM do
      let nms ← chooseNames ctx ci.type
      peel ctx ci.type #[] #[] nms
    let defs ← liftTermElabM <| reached.mapM fun d => (explain ctx d : MetaM String)
    out := out.push s!"## {code (tidy ctx hn.toString)}"
    out := out.push ""
    out := out.push s!"Full name {code hn.toString}."
    out := out.push ""
    -- generated status (run 2026-11-18T0228Z, `runs/2026-11-18T0228Z/t5/READERS.md`): blind readers dropped a
    -- valid headline 3/3 when one labelled paraphrase line (or one STATE.md line) said it was withdrawn,
    -- because nothing generated said anything about status; this line is computed here, so a status
    -- sentence in author prose now contradicts a generated line
    let axs := (← collectAxioms hn).qsort (fun a b => a.toString < b.toString)
    for ax in axs do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        errors := errors.push s!"{hn} uses the non-standard axiom {ax}"
    let modName := match env.getModuleIdxFor? hn with
      | some i => env.header.moduleNames[i.toNat]!.toString
      | none => "?"
    -- fidelity record (run 2026-11-18T0828Z; see the setup above)
    let (nw, ob, k) ← liftTermElabM do
      return (← Checked.Trust.needsWitness ci.type, ← Checked.Trust.nvObligation ci.type,
        ← Checked.Trust.numHyps ci.type)
    let nvPart ← do
      if !nw then pure "non-vacuity: nothing to witness (the statement has no hypothesis to meet)"
      else
        let okTy := ob.isAppOf ``Exists || ob.isAppOf ``And || ob.isConstOf ``True
        let ws := if okTy then findThm ob hn else #[]
        let same := fun (n : Name) => n.componentsRev.head!.toString.endsWith hn.componentsRev.head!.toString
        match (ws.find? same).orElse fun _ => ws[0]? with
        | some w => pure s!"non-vacuity: the Checked theorem {code w.toString} states the obligation `Checked.Trust.nvObligation` computes from the statement (data exist that meet its hypotheses)"
        | none =>
          errors := errors.push s!"{hn}: no non-vacuity witness"
          pure "non-vacuity: NO WITNESS"
    let mut nNeed := 0
    let mut nRed := 0
    let mut nData := 0
    let mut nOpen := 0
    for i in [1:k+1] do
      let obs ← liftTermElabM do
        try
          return some (← Checked.Trust.necObligation ci.type i, ← Checked.Trust.dropObligation ci.type i)
        catch _ => return none
      match obs with
      | none => nData := nData + 1
      | some (ne, dr) =>
        if !(findThm ne hn).isEmpty then nNeed := nNeed + 1
        else if !(findThm dr hn).isEmpty then nRed := nRed + 1
        else nOpen := nOpen + 1
    let necPart := if k == 0 then "hypotheses: none numbered"
      else s!"hypotheses: {k} numbered; {nNeed} shown needed (a Checked example meets every other hypothesis and the conclusion fails), {nRed} shown redundant (the statement is proved without it, one at a time), {nData} with no obligation (instance or proof used as data), {nOpen} open (per hypothesis: `TRUST_MAP.md`, section \"Hypothesis necessity\")"
    let rdrs := (litReaders.find? hn).getD #[]
    let srcs := (litSources.find? hn).getD #[]
    let srcPart := if srcs.isEmpty then "" else s!" (source names backed by the readers: {", ".intercalate srcs.toList})"
    -- the readings themselves (run 2026-11-19T0828Z, part 3, `runs/2026-11-19T0828Z/t5/READERS_LN.md`): blind
    -- readers carried a doubt from a hand-written line relating a statement to a NAMED source 3/3 (arm L2) and
    -- from the same relation with no source 0/3 (arm N): they refuted what they could test against the
    -- generated statement and kept what needed the source, which the page did not show. Printing each blind
    -- reader's definition, as the reader wrote it from the source, puts the source's own form on the page
    let rdrTxt ← liftTermElabM <| rdrs.mapM fun rn => do
      match (← getEnv).find? rn with
      | some (.defnInfo d) => return s!"{code (tidy ctx rn.toString)} := {code (← ppE ctx d.value)}"
      | _ => return code (tidy ctx rn.toString)
    let litPart := if rdrs.isEmpty then "statement literals: no blind second reading registered"
      else s!"statement literals: {rdrs.size} definitions written by a blind second reader of the source are registered for this statement in `scripts/trust/literal_readings.txt` and occur in it (`check_literals.py`){srcPart} (printed at the head of this line)"
    -- test L2R (same run, `runs/2026-11-19T0828Z/t5/READERS_L2R.md`): printed at the end of this line, no reader saw
    -- them (3/3 kept the doubt); they now open the line, before the kernel status every reader quotes
    let srcHead := if rdrs.isEmpty then ""
      else s!"**The source's own form, as a blind reader wrote it from the source without seeing this statement (each body occurs in the statement below, `check_literals.py`):** {"; ".intercalate rdrTxt.toList}. "
    let basePart := match litBase.find? hn with
      | some m => s!"; {m} literals of the statement are grandfathered as never read twice (`scripts/trust/literal_baseline.txt`)"
      | none => "; no literal of the statement is grandfathered as unread (`check_literals.py` requires every other literal to be read twice or certified by the proof)"
    let objs := (objections.find? hn).getD #[]
    let closed := (closedObjs.find? hn).getD #[]
    let closedPart := if closed.isEmpty then ""
      else s!"fidelity objections closed on record (`scripts/trust/objections.txt`; an entry is closed only as the header of this page says): {closed.size}: {"; ".intercalate closed.toList}; "
    let objPart := closedPart ++ if objs.isEmpty
      then "open fidelity objections on record (`scripts/trust/objections.txt`, where every objection to the meaning of a listed headline is entered when it is first written anywhere): none"
      else s!"OPEN FIDELITY OBJECTIONS on record (`scripts/trust/objections.txt`): {objs.size}: {"; ".intercalate objs.toList}"
    unless frozenNames.contains hn do
      errors := errors.push s!"{hn} has no fingerprint in scripts/trust/frozen.txt"
    -- split of the record (run 2026-11-26T2028Z, part 3; section Next of runs/2026-11-26T1428Z/README.md): runs
    -- 0228Z, 0828Z and 1428Z showed that every check on a reading certifies its route, not its author, so a copy
    -- of the headline passes as a blind reading. What the kernel re-derives from the statement (the obligations
    -- `nvObligation`, `necObligation`, `dropObligation` are computed from it) holds whoever wrote anything; the
    -- rest is evidence only as far as its writers were independent. The line now says which is which, and the
    -- header counts headlines whose part A is complete (the trust metric of this split).
    -- shape entries (assumptions the numbering does not reach, or reaches only as a bundle), read from
    -- `.lake/necessity_shape.tsv`, which StatementDeps.lean writes (CI and `records_check.py` run it first)
    let shp := (shapes.get? hn.toString).getD ""
    let aDone := (!nw || nvPart.startsWith "non-vacuity: the Checked theorem") && nOpen == 0 && shp.isEmpty
    if aDone then nAComplete := nAComplete + 1
    totNum := totNum + k; totNeed := totNeed + nNeed; totRed := totRed + nRed; totData := totData + nData; totOpen := totOpen + nOpen
    let nPin := (defs.filter fun l => (l.splitOn "— **PINNED**").length > 1).size
    let nSec := (defs.filter fun l => (l.splitOn "blind second formulation (").length > 1 ||
      (l.splitOn "independent blind second reading of the source").length > 1).size
    let nBare := defs.size - nPin - nSec
    totPin := totPin + nPin; totSec := totSec + nSec; totBare := totBare + nBare
    if !rdrs.isEmpty then nWithRdr := nWithRdr + 1
    if (litBase.find? hn).isSome then nWithBase := nWithBase + 1
    if !objs.isEmpty then nWithObj := nWithObj + 1
    let shpPart := if shp.isEmpty then "no assumption outside the numbering (`TRUST_MAP.md`, shape)"
      else s!"assumptions the numbering does not reach or reaches only formally (`TRUST_MAP.md`, shape): {shp}"
    let why := (if nOpen > 0 then [s!"{nOpen} hypotheses open"] else []) ++
      (if nw && !nvPart.startsWith "non-vacuity: the Checked theorem" then ["no non-vacuity witness"] else []) ++
      (if shp.isEmpty then [] else ["shape entries"])
    let aState := if aDone then "part A complete"
      else s!"PART A INCOMPLETE ({", ".intercalate why})"
    let defPart := if defs.isEmpty then "program definitions the claim uses: none"
      else s!"program definitions the claim uses (listed under the claim): {nPin} pinned by a specification the program wrote (the kernel checks that the specification determines the definition, not that it says what the source means), {nSec} with a blind second reading or formulation, {nBare} with neither (only the formula printed is checked)"
    out := out.push s!"**Status (generated):** {srcHead}the statement is proved in module {code modName} of `Checked`; axioms, computed by Lean when this page was generated: {", ".intercalate (axs.toList.map fun a => code a.toString)}. This status is decided by Lean and the registry `scripts/trust/headlines.txt`, never by prose: a headline is withdrawn only by removing it from `Checked` and the registry, which removes it from this page. **Fidelity record (generated; what has been machine-checked about what the statement means, not a proof that it matches its source), in two parts. (A) Re-derived by the kernel from the statement; holds whoever wrote the statement, its witnesses and its proofs; shows the statement is not vacuous and which hypotheses matter, not that it says what its source says:** {nvPart}; {necPart}; {shpPart}; {aState}. **(B) Rests on who wrote a statement; CI checks the route of each item (commit order, briefs without the answer), not that its writer was independent of the authors, so each item is evidence of meaning only as far as that independence holds:** {objPart}; {litPart}{basePart}; {defPart}. The statement is frozen (`scripts/trust/frozen.txt`): changing it needs a `LEDGER.md` entry naming it (`check_relock.py`), and a changed statement changes the claim on this page. CI regenerates this page on every push and fails if the committed copy differs, so it cannot lag the Lean sources."
    out := out.push ""
    if !data.isEmpty then
      out := out.push s!"**For every** {", ".intercalate data.toList}:"
      out := out.push ""
    if !hyps.isEmpty then
      out := out.push "**assuming**"
      out := out.push ""
      for (h, i) in hyps.zipIdx do out := out.push s!"{i + 1}. {h}"
      out := out.push ""
    out := out.push (if hyps.isEmpty && data.isEmpty then "**It holds that**" else "**then**")
    out := out.push ""
    if concl.size == 1 then out := out.push s!"- {concl[0]!}"
    else for (c, i) in concl.zipIdx do out := out.push s!"{i + 1}. {c}"
    out := out.push ""
    if !defs.isEmpty then
      out := out.push "Program definitions in this claim:"
      out := out.push ""
      out := out ++ defs
      out := out.push ""
    let pStart := out.size
    out := out.push "Author's paraphrase (docstring; not generated, checked only by the prose rules):"
    out := out.push ""
    out := out ++ ((doc.trimAscii.copy.splitOn "\n").toArray.map fun l => "> " ++ l.trimAscii.copy)
    out := out.push ""
    paraSpans := paraSpans.push (pStart, out.size)
    nDone := nDone + 1
  -- the split totals (run 2026-11-26T2028Z) replace the placeholder line of the header
  let totals := s!"**Split totals (generated):** {nDone} headlines. Part A complete (non-vacuity witnessed or nothing to witness, no numbered hypothesis open, no shape entry): **{nAComplete}/{nDone}**; numbered hypotheses {totNum}: {totNeed} shown needed, {totRed} shown redundant, {totData} data, {totOpen} open. Part B (never counted as machine-checked): {nWithRdr} headlines with a registered blind reading of their literals, {nWithBase} with literals grandfathered as never read twice, {nWithObj} with an open objection on record; definition uses: {totPin} pinned by a specification the program wrote, {totSec} with a blind second reading or formulation, {totBare} with neither."
  let splitIdx := (out.toList.take hdrEnd).findIdx? (· == "SPLIT_TOTALS")
  match splitIdx with
  | some i => out := out.set! i totals
  | none => errors := errors.push "CLAIMS.md: SPLIT_TOTALS placeholder not found in the header"
  IO.FS.writeFile "CLAIMS.md" (String.intercalate "\n" out.toList ++ "\n")
  -- CLAIMS_READER.md: a fixed header, then exactly the lines of CLAIMS.md after its header that lie in no paraphrase
  -- block; the page README.md and STATE.md send readers to (goal guard). Blind readers of the paraphrase-free page
  -- answered as accurately as readers of CLAIMS.md (0 errors each, 3 + 3 readers, run 2026-11-18T0828Z), and a
  -- labelled author line that nothing generated contradicts misled readers whatever its label (runs
  -- 2026-11-15T1628Z, 2026-11-18T0228Z, 2026-11-18T0828Z): on this page no author sentence stands next to a claim.
  let mut rd : Array String := #[
    "# CLAIMS, reader page (generated by `scripts/trust/Claims.lean`; do not edit by hand)", "",
    "What each headline theorem claims, **generated mechanically from its Lean statement**: this is `CLAIMS.md`",
    "without the authors' docstring paraphrases. Every sentence on this page is printed from Lean or is fixed",
    "generator text, except the phrase of a pinned definition (`scripts/trust/phrases.txt`: frozen, linted in CI,",
    "no formula in it, and always followed by the definition printed from Lean). **There is no author prose on",
    "this page**, and nothing written elsewhere (a docstring, `STATE.md`, a run record) changes what it says. CI",
    "regenerates it on every push and fails if the committed copy differs.", "",
    "**Status:** every headline on this page carries a generated Status line (its `Checked` module and the axioms",
    "Lean computes for it). A headline listed here is proved; a withdrawn headline is removed from `Checked` and",
    "from this page. The Status line also carries the headline's **fidelity record**, generated from Lean and the",
    "registries CI checks: a non-vacuity witness, how many hypotheses are shown needed or redundant, blind second",
    "readings of its literals, and its freeze. None of these proves that a statement matches its source.",
    "**The record is printed in two parts** (run 2026-11-26T2028Z): **(A)** what the kernel re-derives from the",
    "statement itself (non-vacuity and hypothesis-necessity obligations computed from the statement, met by Checked",
    "theorems), which holds whoever wrote the statement, the witnesses and the proofs; **(B)** what rests on who",
    "wrote a statement (objection entries, blind readings, pinning specifications, second readings of definitions),",
    "which CI checks by route only. Part A does not show that the statement says what its source says; part B is",
    "the only evidence of that, and only as far as its writers were independent of the authors (THE RESULT part 4).",
    "SPLIT_TOTALS",
    "**What CI checks about a blind second reading is its route, not that its reader was blind:** its brief was",
    "committed before it and holds none of its numbers, and it was committed alone before its copy in `Checked`;",
    "a reading the authors wrote themselves, even a copy of the headline's own statement, passes the same checks",
    "(run 2026-11-26T1428Z). The record",
    "opens with the headline's open fidelity objections from `scripts/trust/objections.txt`, where every objection to",
    "the meaning of a listed headline is entered when it is first written anywhere (since run 2026-11-18T0828Z): an",
    "objection that is not shown there has not been recorded as one. An objection's own words are author prose and",
    "are not printed: the record shows that it is open and where it is written. An objection leaves the record only",
    "when its headline is re-frozen (its claim changes) or withdrawn. No entry, reading or theorem marks an objection",
    "settled: closure by a Lean theorem that a second reading of the source is equivalent to the headline was tested",
    "and abandoned, because a copy of the headline's statement passes as such a reading (runs 2026-11-26T0228Z, 0828Z",
    "and 1428Z); the generator of this page fails on any closure field.", ""]
  -- the notation and total-function paragraphs of the header are copied (they are fixed generator text)
  let notIdx := (out.toList.take hdrEnd).findIdx? (·.startsWith "Notation (Lean/Mathlib")
  match notIdx with
  | some i => rd := rd ++ (out.extract i hdrEnd)
  | none => errors := errors.push "CLAIMS_READER.md: notation paragraph not found in the header"
  let mut cur := hdrEnd
  for (a, b) in paraSpans do
    rd := rd ++ out.extract cur a
    cur := b
  rd := rd ++ out.extract cur out.size
  for l in rd do
    if l.startsWith "> " || l.startsWith "Author's paraphrase" then
      errors := errors.push s!"CLAIMS_READER.md: a paraphrase line reached the reader page: {l}"
  rd := rd.map fun l => if l == "SPLIT_TOTALS" then totals else l
  IO.FS.writeFile "CLAIMS_READER.md" (String.intercalate "\n" rd.toList ++ "\n")
  -- PHRASE_LINES.md (rule P13, run 2026-11-09T1828Z): every certified reader line with its theorem's generated claim
  let mut pout : Array String := #[
    "# PHRASE LINES (generated by `scripts/trust/Claims.lean`; do not edit by hand)", "",
    "The phrase of a pinned definition in a generated claim (CLAIMS.md) is a sequence of lines written by blind",
    "readers (`scripts/trust/phrase_roles.txt`). Each line below is proved about the Lean definition by the Checked",
    "theorem named under it (`scripts/trust/phrase_certs.txt`, rule P13 of `scripts/trust/check_claims.py`); its",
    "statement is generated from Lean exactly as in CLAIMS.md. **The line holds as stated here, under these",
    "assumptions, and not beyond them.** Reader lines shown without such a theorem are listed in the shrink-only",
    "`scripts/trust/phrase_cert_baseline.txt`. CI fails if this file differs from the generator's output.", ""]
  for (dn, kind, line, tn) in certList do
    let tc := (env.find? tn).get!
    let (data, hyps, concl) ← liftTermElabM do
      let nms ← chooseNames ctx tc.type
      peel ctx tc.type #[] #[] nms
    pout := pout.push s!"## {code (tidy ctx dn.toString)}: «{line}» ({kind})"
    pout := pout.push ""
    pout := pout.push s!"Theorem {code tn.toString}."
    pout := pout.push ""
    if !data.isEmpty then
      pout := pout.push s!"**For every** {", ".intercalate data.toList}:"
      pout := pout.push ""
    if !hyps.isEmpty then
      pout := pout.push "**assuming**"
      pout := pout.push ""
      for (h, i) in hyps.zipIdx do pout := pout.push s!"{i + 1}. {h}"
      pout := pout.push ""
    pout := pout.push (if hyps.isEmpty && data.isEmpty then "**It holds that**" else "**then**")
    pout := pout.push ""
    if concl.size == 1 then pout := pout.push s!"- {concl[0]!}"
    else for (c, i) in concl.zipIdx do pout := pout.push s!"{i + 1}. {c}"
    pout := pout.push ""
  IO.FS.writeFile "PHRASE_LINES.md" (String.intercalate "\n" pout.toList ++ "\n")
  -- phrase data for the linter (scripts/trust/check_claims.py)
  let mut pl : Array String := #[]
  for (d, tmpl) in phrases.toList do
    let dc := (env.find? d).get!
    let own := (deps env stop (dc.value?.getD (.sort 0)) (deps env stop dc.type {})).toList.filter
      (fun n => stop.contains n && n != d)
    -- the pinning specification's own text (run 2026-11-08T1828Z, rule P2 of check_claims.py, after blind
    -- red team Y: words in a phrase that no check reads, "conformal", "fitted value 0.3", swapped equation
    -- numbers): the docstrings and field names of the program constants the pin theorem's statement uses
    -- other than pinned definitions (the SPEC structure or blind formulation, written by a blind spec
    -- writer), not the pin theorem's own docstring
    let mut spec : Array String := #[]
    let inFid := fun (c : Name) => match env.getModuleIdxFor? c with
      | some idx => (`Checked.Fidelity).isPrefixOf (env.header.moduleNames[idx.toNat]!)
      | none => false
    if let some pin := pinned.find? d then
      if let some pc := env.find? pin then
        -- specification constants: definitions and structures of `Checked.Fidelity` modules that the pin
        -- theorem's statement uses, and those their field types or bodies use (two levels), never a theorem
        let mut todo : Array (Name × Nat) := (pc.type.getUsedConstants.filter fun c =>
          inFid c && !stop.contains c).map (·, 0)
        let mut seen : NameSet := {}
        while !todo.isEmpty do
          let (c, k) := todo.back!
          todo := todo.pop
          if seen.contains c then continue
          seen := seen.insert c
          let some ci := env.find? c | continue
          let isThm := match ci with | .thmInfo _ => true | _ => false
          if isThm then continue
          spec := spec.push c.componentsRev.head!.toString
          if let some s := (← findDocString? env c) then spec := spec.push s
          let mut inner : Array Name := match ci with
            | .defnInfo dv => dv.value.getUsedConstants
            | _ => #[]
          if isStructure env c then
            for f in getStructureFields env c do
              spec := spec.push f.toString
              if let some s := (← findDocString? env (c ++ f)) then spec := spec.push s
              if let some fi := env.find? (c ++ f) then inner := inner ++ fi.type.getUsedConstants
          if k < 2 then
            for c' in inner do
              if inFid c' && !stop.contains c' && !seen.contains c' then todo := todo.push (c', k + 1)
    pl := pl.push (Json.mkObj [("name", toString d), ("short", d.componentsRev.head!.toString),
      ("phrase", tmpl), ("rests_on", toJson (own.map fun n => n.componentsRev.head!.toString)),
      ("spec_text", toJson (" ".intercalate spec.toList))]).compress
  IO.FS.createDirAll ".lake"
  IO.FS.writeFile ".lake/phrases.jsonl" (String.intercalate "\n" pl.toList ++ "\n")
  logInfo m!"CLAIMS.md: {nDone} generated claims"
  unless errors.isEmpty do
    throwError m!"claims generator errors:\n{String.intercalate "\n" errors.toList}"
