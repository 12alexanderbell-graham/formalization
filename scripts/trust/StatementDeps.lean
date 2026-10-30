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
The UNPINNED report is informational (annex LIV: report first, block later).

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
  !n.isInternal && !(Lean.Meta.isMatcherCore env n) && !env.isProjectionFn n &&
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

end StatementDeps

open StatementDeps in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  -- candidate non-vacuity witnesses: Checked theorems whose statement is an `∃` or `True`
  let nvCands : Array (Name × Expr) := env.constants.map₁.fold (init := #[]) fun acc n ci =>
    if isCheckedConst env n && !n.isInternal then
      match ci with
      | .thmInfo t =>
        if t.type.isAppOf ``Exists || t.type.isConstOf ``True then acc.push (n, t.type) else acc
      | _ => acc
    else acc
  let mut nNeed := 0
  let mut nWit := 0
  let cands : Array Name := env.constants.map₁.fold (init := #[]) fun acc n _ =>
    if isCheckedConst env n && !n.isInternal then acc.push n else acc
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
          if k == "UNCLASSIFIED" then unclassified := unclassified.insert d
        else if k == "PRINTED" || k == "CLAIM" then transcr := transcr.push short
      if gaps.isEmpty then nClean := nClean + 1
      let shortH := (hn.toString.replace "Checked.Cosmography." "").replace "Checked." ""
      let fmt (a : Array String) : String := if a.isEmpty then "—" else ", ".intercalate a.toList
      rows := rows.push s!"| `{shortH}` | {fmt pins} | {fmt gaps} | {fmt transcr} | {nvCol} |"
      logInfo m!"{hn}\n{String.intercalate "\n" lines.toList}"
  let summary := gapCount.toList.toArray.qsort (fun a b => a.2 > b.2)
  let summaryLines := summary.toList.map fun (n, k) => s!"| `{n}` | {k} |"
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
