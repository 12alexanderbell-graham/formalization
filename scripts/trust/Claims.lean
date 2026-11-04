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
* every program definition the statement reaches is listed: PINNED ones with their phrase and pin
  theorem, all others with their kind and their full body (Prop-valued bodies rendered in words).
The author's docstring is shown last, labelled as an unchecked paraphrase.

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
  /-- full name ↦ displayed name, longest full names first -/
  short : Array (String × String)

/-- Collapse whitespace (the pretty-printer breaks long lines). -/
def oneLine (s : String) : String :=
  " ".intercalate ((s.split (fun c => c == '\n' || c == ' ')).toList.map (·.toString) |>.filter (· ≠ ""))

def tidy (ctx : Ctx) (s : String) : String :=
  ctx.short.foldl (fun s (f, sh) => s.replace f sh) s

def ppE (ctx : Ctx) (e : Expr) : MetaM String := do
  let f ← withOptions (fun o => (o.setBool `pp.proofs false).set `format.width (100000 : Nat)) <| ppExpr e
  return tidy ctx (oneLine (toString f))

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
          let vals ← args.mapM fun a => do return code (← ppE ctx a)
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

/-- Leading binders: data binders, rendered assumptions, then the conclusion. -/
partial def peel (ctx : Ctx) (ty : Expr) (data hyps : Array String) :
    MetaM (Array String × Array String × Array String) := do
  match (← instantiateMVars ty).consumeMData with
  | .forallE n d b bi =>
    withLocalDecl n bi d fun x => do
      let nm := (← x.fvarId!.getUserName).eraseMacroScopes
      let b' := b.instantiate1 x
      if bi.isInstImplicit then
        peel ctx b' data (hyps.push s!"(instance) {code (← ppE ctx d)}")
      else if (← isProp d) then
        peel ctx b' data (hyps.push (← renderProp ctx d))
      else
        peel ctx b' (data.push (code s!"{nm} : {← ppE ctx d}")) hyps
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
    forallTelescope ci.type fun xs _ => do
      let names ← xs.mapM fun x => return (← x.fvarId!.getUserName).eraseMacroScopes.toString
      let head ← ppE ctx (mkAppN (.const d (ci.levelParams.map Level.param)) xs)
      let vals := names.map code
      return s!"- {code head} — **PINNED** (pin theorem {code (tidy ctx pin.toString)}): {fill tmpl names vals}"
  | none =>
    let kind := (ctx.kinds.find? d).getD "UNCLASSIFIED"
    match ci with
    | .defnInfo dv =>
      lambdaTelescope dv.value fun xs body => do
        let head ← ppE ctx (mkAppN (.const d (ci.levelParams.map Level.param)) xs)
        let sig ← xs.mapM fun x => do return code s!"{(← x.fvarId!.getUserName).eraseMacroScopes} : {← ppE ctx (← inferType x)}"
        let sigTxt := if sig.isEmpty then "" else s!" (for {", ".intercalate sig.toList})"
        if ← isProp body then
          return s!"- {code head} — {kind}, not pinned{sigTxt}: means {← renderProp ctx body}"
        else
          return s!"- {code head} — {kind}, not pinned{sigTxt}: is defined as {code (← ppE ctx body)}"
    | .inductInfo iv =>
      let cs ← iv.ctors.mapM fun k => do return code s!"{tidy ctx k.toString} : {← ppE ctx (← getConstInfo k).type}"
      return s!"- {code shortD} — {kind}, not pinned: inductive type with constructors {", ".intercalate cs}"
    | _ => return s!"- {code shortD} — {kind}, not pinned: {code (← ppE ctx ci.type)}"

end Claims

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
  let shown := reachedAll.toList ++ hs.toList ++ pinned.toList.map (·.2)
  -- display name: the shortest dotted suffix that no other shown constant shares
  let suffix := fun (n : Name) (k : Nat) => ".".intercalate ((n.components.map toString).drop (n.components.length - k))
  let short : Array (String × String) := (shown.map fun n =>
    let k := (List.range n.components.length).map (· + 1) |>.find? (fun k =>
      !(shown.any fun m => m != n && (m.toString == suffix n k || m.toString.endsWith ("." ++ suffix n k))))
    (n.toString, suffix n (k.getD n.components.length))).toArray.qsort (fun a b => a.1.length > b.1.length)
  let ctx : Ctx := { pinned, kinds, phrases, short }
  let mut out : Array String := #[
    "# CLAIMS (generated by `scripts/trust/Claims.lean`; do not edit by hand)", "",
    "What each headline theorem claims, **generated mechanically from its Lean statement** (run",
    "2026-11-04T2228Z). The logical structure (for every, assuming, then, and, or, it is false that,",
    "there is) is spelled out by the generator; formulas are printed verbatim by Lean in code spans;",
    "the only hand-written words are the phrases of pinned definitions (`scripts/trust/phrases.txt`,",
    "frozen and linted in CI). Every program definition a claim uses is listed under it: pinned ones",
    "with their phrase, all others with their full definition. The author's docstring follows,",
    "labelled as a paraphrase: **where the paraphrase and the generated claim differ, the generated",
    "claim is what was proved.** CI fails if this file differs from the generator's output.", "",
    "Notation (Lean/Mathlib, printed as is): `Set.Icc a b` = [a, b]; `Set.Ioo a b` = (a, b);",
    "`√x` = square root; `Real.log` = natural logarithm; `Real.logb b x` = log base b; `deriv f x` =",
    "derivative; `iteratedDeriv n f x` = n-th derivative; `HasDerivAt f f' x` = f has derivative f' at",
    "x; `HasDerivWithinAt f f' s x` = derivative within the set s; `∫ x in a..b, f x` = integral from",
    "a to b; `∀ᶠ t in 𝓝 t₀, P t` = P holds on some neighbourhood of t₀; `f =o[𝓝 x] g` = f is little-o",
    "of g as the argument tends to x; `RoundsTo x d k` = x rounds to the decimal d at k places;",
    "`ContDiffAt ℝ n f x` = f is n times continuously differentiable at x; `87e-3` = 87·10⁻³ = 0.087;",
    "`nhds x` = `𝓝 x`; `deriv^[n] f` = n-th derivative of f.", ""]
  let mut nDone := 0
  for hn in hs do
    let ci := (env.find? hn).get!
    let doc := (← findDocString? env hn).getD ""
    let reached := (deps env stop ci.type {}).toList.filter (reportable env) |>.toArray.qsort
      (fun a b => tidy ctx a.toString < tidy ctx b.toString)
    for d in reached do
      if pinned.contains d && !phrases.contains d then
        errors := errors.push s!"{hn} reaches the pinned {d}, which has no phrase in scripts/trust/phrases.txt"
    let (data, hyps, concl) ← liftTermElabM <| peel ctx ci.type #[] #[]
    let defs ← liftTermElabM <| reached.mapM fun d => (explain ctx d : MetaM String)
    out := out.push s!"## {code (tidy ctx hn.toString)}"
    out := out.push ""
    out := out.push s!"Full name {code hn.toString}."
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
    out := out.push "Author's paraphrase (docstring; not generated, checked only by the prose rules):"
    out := out.push ""
    out := out ++ ((doc.trimAscii.copy.splitOn "\n").toArray.map fun l => "> " ++ l.trimAscii.copy)
    out := out.push ""
    nDone := nDone + 1
  IO.FS.writeFile "CLAIMS.md" (String.intercalate "\n" out.toList ++ "\n")
  -- phrase data for the linter (scripts/trust/check_claims.py)
  let mut pl : Array String := #[]
  for (d, tmpl) in phrases.toList do
    let dc := (env.find? d).get!
    let own := (deps env stop (dc.value?.getD (.sort 0)) (deps env stop dc.type {})).toList.filter
      (fun n => stop.contains n && n != d)
    pl := pl.push (Json.mkObj [("name", toString d), ("short", d.componentsRev.head!.toString),
      ("phrase", tmpl), ("rests_on", toJson (own.map fun n => n.componentsRev.head!.toString))]).compress
  IO.FS.createDirAll ".lake"
  IO.FS.writeFile ".lake/phrases.jsonl" (String.intercalate "\n" pl.toList ++ "\n")
  logInfo m!"CLAIMS.md: {nDone} generated claims"
  unless errors.isEmpty do
    throwError m!"claims generator errors:\n{String.intercalate "\n" errors.toList}"
