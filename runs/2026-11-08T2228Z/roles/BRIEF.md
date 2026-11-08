# Brief: blind role reader for the pinned definitions (run 2026-11-08T2228Z)

You are a blind reader. The program has 23 *pinned* definitions: Lean definitions whose meaning is fixed by a
pinning theorem that derives them from a specification (SPEC) written by other blind writers. Your job is to say,
for every argument (binder) of every definition below, **what that argument is** — its physical or mathematical
role — reading the specification and the pinning theorem, and to say which **sign conventions** the specification
fixes. Your answers will be compared mechanically with text written by someone else, so be exact and plain.

## What you may read
- `Checked/Fidelity/*.lean`, `Checked/Sim/DuffingPin.lean`, `Checked/Sim/MMPin.lean`, `Checked/Sim/RobPin.lean`
  (the specifications and pinning theorems; find each pin theorem below with grep).
- The Lean source of each definition (its signature and body) under `Checked/` (find it with grep), and the Lean
  sources it uses.

## What you must NOT read
`scripts/` (everything in it), every `*.md` file in the repository (README, STATE, CLAIMS, TRUST_MAP,
TRUSTED_DEFINITIONS, FINDINGS, LEDGER, CHANGELOG, …), `validation/`, `runs/` (except this folder), `Work/`, `_archive/`,
and the git history. Do not use the web.

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

## How to decide a role
Use the pinning theorem to see which specification argument each program argument is passed to, then read what
the specification's laws and docstrings do with it (e.g. which time is the one at which light is received, which
function is differentiated, which constant multiplies which product). Where the specification is silent, use the
definition's Lean body (never its docstring or name). Distinguish arguments that look alike (two times, two
volumes, several rate constants, several initial values, several unknown functions): each role must say what
tells this argument apart from the others.

## Output (write exactly one file: `runs/2026-11-08T2228Z/roles/ROLES.txt`)
One line per binder of every definition, in the order above, and nothing else except optional `SIGN` lines:

    ROLE | <full Lean name> | <binder> | <role>

- `<role>`: a plain-English noun phrase of 1 to 6 words, lowercase except proper names and chemical/species letters,
  no formula characters (no = + - / * ^ < > ′ digits-as-operators), no symbols of other binders, no articles at
  the start (write `observation time`, not `the observation time`). Examples of the *form* (not answers):
  `emission time`, `curvature constant`, `scale factor`, `initial velocity`, `rate constant of the first reaction`.
- If two binders would get the same words, add the distinguishing words (`initial concentration of species B`).

Then, for each definition whose specification fixes a sign convention or a relation to a named symbol (for example
"this quantity is minus X", "positive for closed universes"), one line:

    SIGN | <full Lean name> | <the convention as a short plain-English clause, 3 to 12 words, no formula characters>

At the end, a line `END` and a one-paragraph note (after `END`) on anything you could not decide.
