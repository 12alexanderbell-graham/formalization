# Brief: blind predicate-shape reader for the pinned definitions (run 2026-11-09T1428Z, second reading)

**Purpose (fixed before any red team of this run ran).** The program generates the claim of every headline
(`CLAIMS.md`) from its Lean statement. A pinned definition is explained there by a short *phrase*. Every word of a
phrase already comes from blind readers (the definition's name, the role of each argument, its sign conventions and
clauses), with one exception: for a definition that is a **property** (a Lean `Prop`: "x is a solution of …", "a obeys
the law …"), the author still chooses which arguments are the *subject* of the sentence, the verb, and the article
before the name. Two rules are planned for this run:
- **P10 (shape)**: the subject, verb and article of every property's phrase come from a blind reader's SHAPE line (yours);
  a definition the reader calls a quantity gets no verb at all.
- **P11 (generated)**: CI regenerates every phrase from the blind registry (names, roles, sign conventions, clauses,
  shapes) with a fixed template and fails unless the phrase file is exactly that output: no word, connective, order or
  mark of a phrase is chosen by the author.
You write the SHAPE lines.

**Why a second reading.** The first shape reader of this run (`runs/2026-11-09T1428Z/shapes/`, which you must not
read) was not given the definitions' names and so chose verbs that do not fit them (a function "is" a law). This time
you are given the NAME of every definition, written by an earlier blind reader: your sentence will read

    the <role of subject> {subject} <verb> <article> <NAME> with the <role> {x}, … and the <role> {y}

(or `the <NAME> holds with …` when the subject is `none`; for a quantity: `the <NAME> with …`). Choose subject, verb
and article so that this sentence is TRUE of the Lean definition, read literally: a function is not a law or a
condition; it obeys a law or satisfies a condition; an "… solution" is something the subject *is*. Your answers will be compared with the Lean definitions by someone else.

You are a blind reader. For each definition below, read its specification, its pinning theorem and its Lean signature
and body, and decide how a scientist would say in one sentence what the definition asserts or denotes.

## What you may read
- `Checked/Fidelity/*.lean`, `Checked/Sim/DuffingPin.lean`, `Checked/Sim/MMPin.lean`, `Checked/Sim/RobPin.lean`
  (the specifications and pinning theorems; find each pin theorem below with grep).
- The Lean source of each definition (its signature and body) under `Checked/` (find it with grep), and the Lean
  sources it uses.

## What you must NOT read
`scripts/` (everything in it), every `*.md` file in the repository other than this brief (README, STATE, CLAIMS,
TRUST_MAP, TRUSTED_DEFINITIONS, FINDINGS, LEDGER, CHANGELOG, PROMPT, …), `validation/`, `runs/` (except this folder),
`Work/`, `_archive/`, and the git history. Do not use the web. Lean docstrings (`/-- … -/`) of the program definitions
themselves are author text: do not take your decisions from them; the specification's own fields, laws and
docstrings are blind text you may use.

## The definitions (Lean name · binders in order · pinning theorem)
1. `Checked.Cosmography.hubble` · a t · `hubbleSpec_pins`
2. `Checked.Cosmography.decel` · a t · `decelSpec_pins`
3. `Checked.Cosmography.BambaK.lumDist` · K a t₀ t · `lumDistSpec2_pins`
4. `Checked.Cosmography.BambaA.angDist` · K a t₀ t · `angDistSpec_pins`
5. `Checked.Cosmography.Aviles.IsFlatLCDM` · Ω a t₀ · `flatLCDMSpec2_pins`
6. `Checked.Cosmography.redshift` · a t₀ t · `redshiftCore_pins`
7. `Checked.Cosmography.Aviles.cosmoCoeff` · n a t · `cosmoCoeffCore_pins`
8. `Checked.Cosmography.BambaY.yred` · a t₀ t · `yRedSpec_pins`
9. `Checked.Cosmography.BambaK.omega0` · K a t₀ · `omega0Spec_pins`
10. `Checked.Cosmography.BambaZ.curvK` · K a t₀ · `curvKSpec_pins`
11. `Checked.Cosmography.BambaY.lumDistFlat` · a t₀ t · `lumDistFlat_pins`
12. `Checked.Cosmography.BambaY.comoving` · a t₀ t · `comoving_pins`
13. `Checked.Cosmography.CPL.IsFlatCPL` · Ω w₀ wₐ a t₀ · `flatCPL_pins`
14. `Checked.Cosmography.FRCosmo.curv` · a t · `ricciSpec_pins`
15. `Checked.Cosmography.FRCosmo.rhoM` · Ω a t₀ t · `rhoM_eq_dust`
16. `Checked.Cosmography.FRCosmo.FriedmannEq` · Ω a F t₀ t · `friedmannEq_iff_blind`
17. `Checked.Cosmography.FRCosmo.MasterEq` · Ω a F t₀ t · `masterEq_iff_blind`
18. `Checked.Cosmography.Transverse.transverse` · K χ · `transverseSpec_pins`
19. `Checked.Chemistry.CubicEOS.IsCriticalIsotherm` · p v · `criticalSpec_pins`
20. `Checked.Chemistry.Coexistence.IsMaxwellCoexistence` · p vl vg ps · `maxwellSpec_pins`
21. `Checked.Sim.Duffing.IsDuffingSolution` · k β x₀ v₀ T x · `duffingSpec_pins`
22. `Checked.Sim.MichaelisMenten.IsMMSolution` · k₁ km₁ k₂ s₀ e₀ c₀ p₀ T s e c p · `mmSpec_pins`
23. `Checked.Sim.Robertson.IsRobSolution` · k₁ k₂ k₃ a₀ b₀ c₀ T y₁ y₂ y₃ · `robSpec_pins`

## The blind NAME of each definition (earlier reader, `runs/2026-11-08T2228Z/names/NAMES.txt`)

    NAME | Checked.Cosmography.hubble | Hubble rate
    NAME | Checked.Cosmography.decel | deceleration parameter
    NAME | Checked.Cosmography.BambaK.lumDist | luminosity distance in FLRW with curvature
    NAME | Checked.Cosmography.BambaA.angDist | angular diameter distance in FLRW with curvature
    NAME | Checked.Cosmography.Aviles.IsFlatLCDM | flat ΛCDM Friedmann expansion law
    NAME | Checked.Cosmography.redshift | cosmological redshift
    NAME | Checked.Cosmography.Aviles.cosmoCoeff | cosmographic coefficient
    NAME | Checked.Cosmography.BambaY.yred | y redshift
    NAME | Checked.Cosmography.BambaK.omega0 | present total density parameter Ω0
    NAME | Checked.Cosmography.BambaZ.curvK | dimensionless spatial curvature parameter
    NAME | Checked.Cosmography.BambaY.lumDistFlat | luminosity distance in flat FLRW
    NAME | Checked.Cosmography.BambaY.comoving | comoving radial distance
    NAME | Checked.Cosmography.CPL.IsFlatCPL | flat matter plus CPL dark energy Friedmann expansion law
    NAME | Checked.Cosmography.FRCosmo.curv | Ricci scalar of flat FLRW
    NAME | Checked.Cosmography.FRCosmo.rhoM | dust matter density
    NAME | Checked.Cosmography.FRCosmo.FriedmannEq | metric F(R) gravity Friedmann equation with dust
    NAME | Checked.Cosmography.FRCosmo.MasterEq | metric F(R) gravity second equation with dust
    NAME | Checked.Cosmography.Transverse.transverse | FLRW transverse distance function
    NAME | Checked.Chemistry.CubicEOS.IsCriticalIsotherm | critical point condition of an isotherm
    NAME | Checked.Chemistry.Coexistence.IsMaxwellCoexistence | Maxwell equal area coexistence condition
    NAME | Checked.Sim.Duffing.IsDuffingSolution | Duffing oscillator initial value problem solution
    NAME | Checked.Sim.MichaelisMenten.IsMMSolution | Michaelis Menten mass action initial value problem solution
    NAME | Checked.Sim.Robertson.IsRobSolution | Robertson chemical kinetics initial value problem solution

## What to decide for each definition
1. **quantity or property.** A *quantity* denotes a value (a number or a function: "the Hubble rate of a at t").
   A *property* is a statement that is true or false of its arguments (Lean type ending in `Prop`).
2. For a property:
   - **subject**: the argument or arguments that the property is *about* — the object(s) that satisfy it, e.g. the
     unknown function(s) of an equation or initial value problem, the function that obeys a law, the function that
     satisfies a condition. The other arguments are parameters, data or evaluation points and will be listed after
     the name with "with". Write the binder symbols exactly as in the list above, space-separated, in the order you
     would name them. Write `none` if the property is an equation or identity among all its arguments with no single
     object that "satisfies" it (the sentence will read "the NAME holds with …").
   - **verb**: exactly one of `is` (one subject that is an instance of the named kind of object, e.g. "x is a
     solution of …"), `are` (several subjects that together are such an object), `obeys` (a subject that obeys a
     law), `satisfies` (a subject that satisfies a condition), `solves`, or `holds` (only with subject `none`).
   - **article** before the definition's name: `a` if many different objects can have the property (one solution
     among possibly many, one instance of a kind), `the` if the name denotes one specific law, condition or equation
     that the subject obeys or satisfies.

## Output (write exactly one file: `runs/2026-11-09T1428Z/shapes2/SHAPES.txt`)
One line per definition, in the order above:

    SHAPE | <full Lean name> | quantity
    SHAPE | <full Lean name> | property | <subject binders or none> | <verb> | <article>

At the end, a line `END` and a one-paragraph note (after `END`) on anything you could not decide.
