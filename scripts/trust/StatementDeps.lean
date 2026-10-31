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

/-- Definitions worth reporting: user-facing `def`s and inductive types, not auxiliary
constants (proof terms, matchers, projections, constructors). -/
def reportable (env : Environment) (n : Name) : Bool :=
  !(privateToUserName n).isInternal && !(Lean.Meta.isMatcherCore env n) && !env.isProjectionFn n &&
  match env.find? n with
  | some (.defnInfo _) => true
  | some (.inductInfo _) => true
  | _ => false

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
  let secondRead : NameSet := env.constants.map₁.fold (init := {}) fun acc n ci =>
    if (`Checked.Trust.Transcriptions).isPrefixOf n then
      match ci with
      | .thmInfo t =>
        match t.type.eq? with
        | some (_, lhs, _) => if lhs.isConst then acc.insert lhs.constName! else acc
        | none => acc
      | _ => acc
    else acc
  let mut nNeed := 0
  let mut nWit := 0
  let cands : Array Name := env.constants.map₁.fold (init := #[]) fun acc n _ =>
    if isCheckedConst env n && !(privateToUserName n).isInternal then acc.push n else acc
  let heads ← readLines "scripts/trust/headlines.txt"
  let pinLines ← readLines "scripts/trust/pins.txt"
  let kindLines ← readLines "scripts/trust/def_kinds.txt"
  let mut errors : Array String := #[]
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
  for h in heads do
    if let .ok hn := resolve cands h then
      frozenNow := frozenNow.insert hn (fingerprint (env.find? hn).get!)
  for (dn, tn) in pinned.toList do
    frozenNow := frozenNow.insert dn (fingerprint (env.find? dn).get!)
    frozenNow := frozenNow.insert tn (fingerprint (env.find? tn).get!)
  for (dn, k) in kinds.toList do
    -- the kind label is frozen too (red team C, defect C07 relabelled PRINTED as FORMULA)
    frozenNow := frozenNow.insert dn (fingerprint (env.find? dn).get! ++ "-" ++ k)
  let frozenLines := (frozenNow.toList.toArray.qsort (fun a b => a.1.toString < b.1.toString)).map
    fun (n, f) => s!"{n} {f}"
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
      match locked.get? n.toString with
      | some f' =>
        if f != f' then
          errors := errors.push s!"FROZEN {n} changed (statement or definition body): if intended, relock (TRUST_RELOCK=1) and name it in a LEDGER.md entry"
      | none => errors := errors.push s!"{n} is not in scripts/trust/frozen.txt: relock (TRUST_RELOCK=1)"
    -- an entry that is no longer registered was removed without relocking (red team C)
    let nowStr : Std.HashSet String := frozenNow.foldl (init := {}) fun s n _ => s.insert n.toString
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
  for h in heads do
    if let .ok hn := resolve cands h then
      if (`Checked.Records).isPrefixOf hn then
        let lits := posRoundsToLits (env.find? hn).get!.type
        if lits.isEmpty then
          errors := errors.push s!"{hn} is in Checked.Records but asserts no RoundsTo"
        if (roundsToLits (env.find? hn).get!.type).size != lits.size then
          errors := errors.push s!"{hn}: a RoundsTo in a position the statement does not assert (under ¬, ∨, ↔ or in a hypothesis)"
        for l in lits do
          match l with
          | some str => recLines := recLines.push s!"{hn.componentsRev.head!}\t{str}"
          | none => errors := errors.push s!"{hn}: a RoundsTo whose value is not a decimal literal with at most k decimals"
  IO.FS.createDirAll ".lake"
  IO.FS.writeFile ".lake/records_numbers.tsv" (String.intercalate "\n" recLines.toList ++ "\n")
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
        match nvCands.find? (fun (n, t) => n != hn && t == ob) with
        | some (w, _) =>
          nWit := nWit + 1
          nvCol := s!"`{w.componentsRev.head!}`"
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
      if gaps.isEmpty then nClean := nClean + 1
      let shortH := (hn.toString.replace "Checked.Cosmography." "").replace "Checked." ""
      let fmt (a : Array String) : String := if a.isEmpty then "—" else ", ".intercalate a.toList
      rows := rows.push s!"| `{shortH}` | {fmt pins} | {fmt gaps} | {fmt transcr} | {nvCol} |"
      logInfo m!"{hn}\n{String.intercalate "\n" lines.toList}"
  let summary := gapCount.toList.toArray.qsort (fun a b => a.2 > b.2)
  let summaryLines := summary.toList.map fun (n, k) => s!"| `{n}` | {k} |"
  let printedDefs := kinds.toList.filter (fun (_, k) => k == "PRINTED")
  let nPrinted := printedDefs.length
  let nSecond := (printedDefs.filter fun (d, _) => secondRead.contains d).length
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
    s!"Transcriptions (trust track T3): {nPrinted} PRINTED definitions; {nSecond} carry a machine-checked",
    "agreement with an independent blind second reading (`Checked/Trust/Transcriptions.lean`; marked ² below).",
    "",
    "## Unpinned physics definitions, by number of headlines resting on them",
    "",
    "| Definition | Headlines |",
    "|---|---|"] ++ summaryLines ++ [
    "",
    "## Per headline",
    "",
    "| Headline | Pinned | Unpinned physics | Transcriptions | Non-vacuity witness |",
    "|---|---|---|---|---|"] ++ rows.toList) ++ "\n"
  IO.FS.writeFile "TRUST_MAP.md" md
  logInfo m!"SUMMARY: {nHeads} headlines; {nClean} rest on no unpinned physics definition; \
    non-vacuity: {nWit}/{nNeed} conditional headlines witnessed.\n\
    {String.intercalate "\n" (summary.toList.map fun (n, k) => s!"  {k}  {n}")}"
  unless unclassified.isEmpty do
    logInfo m!"UNCLASSIFIED (add to scripts/trust/def_kinds.txt): {unclassified.toList}"
  unless errors.isEmpty do
    throwError m!"statement-dependency registry errors:\n{String.intercalate "\n" errors.toList}"
