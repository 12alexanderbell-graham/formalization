# Brief: blind name reader for the pinned definitions (run 2026-11-08T2228Z)

You are a blind reader. The program has 23 *pinned* definitions: Lean definitions whose meaning is fixed by a
pinning theorem that derives them from a specification (SPEC) written by other blind writers. Your job is to say,
for every definition below, **what it is** in a short standard name — the quantity it computes or the property it
states — including every qualifier that restricts it (for example spatial flatness, the model or law it belongs
to, the kind of distance), reading the specification and the pinning theorem. Your answers will be compared
mechanically with text written by someone else, so be exact and plain.

## What you may read
- `Checked/Fidelity/*.lean`, `Checked/Sim/DuffingPin.lean`, `Checked/Sim/MMPin.lean`, `Checked/Sim/RobPin.lean`
  (the specifications and pinning theorems; find each pin theorem below with grep).
- The Lean source of each definition (its signature and body) under `Checked/` (find it with grep), and the Lean
  sources it uses.

## What you must NOT read
`scripts/` (everything in it), every `*.md` file in the repository except this brief, `validation/`, `runs/`
(except this folder), `Work/`, `_archive/`, and the git history. Do not use the web.

## The definitions (Lean name · pinning theorem)
1. `Checked.Cosmography.hubble` · `hubbleSpec_pins`
2. `Checked.Cosmography.decel` · `decelSpec_pins`
3. `Checked.Cosmography.BambaK.lumDist` · `lumDistSpec2_pins`
4. `Checked.Cosmography.BambaA.angDist` · `angDistSpec_pins`
5. `Checked.Cosmography.Aviles.IsFlatLCDM` · `flatLCDMSpec2_pins`
6. `Checked.Cosmography.redshift` · `redshiftCore_pins`
7. `Checked.Cosmography.Aviles.cosmoCoeff` · `cosmoCoeffCore_pins`
8. `Checked.Cosmography.BambaY.yred` · `yRedSpec_pins`
9. `Checked.Cosmography.BambaK.omega0` · `omega0Spec_pins`
10. `Checked.Cosmography.BambaZ.curvK` · `curvKSpec_pins`
11. `Checked.Cosmography.BambaY.lumDistFlat` · `lumDistFlat_pins`
12. `Checked.Cosmography.BambaY.comoving` · `comoving_pins`
13. `Checked.Cosmography.CPL.IsFlatCPL` · `flatCPL_pins`
14. `Checked.Cosmography.FRCosmo.curv` · `ricciSpec_pins`
15. `Checked.Cosmography.FRCosmo.rhoM` · `rhoM_eq_dust`
16. `Checked.Cosmography.FRCosmo.FriedmannEq` · `friedmannEq_iff_blind`
17. `Checked.Cosmography.FRCosmo.MasterEq` · `masterEq_iff_blind`
18. `Checked.Cosmography.Transverse.transverse` · `transverseSpec_pins`
19. `Checked.Chemistry.CubicEOS.IsCriticalIsotherm` · `criticalSpec_pins`
20. `Checked.Chemistry.Coexistence.IsMaxwellCoexistence` · `maxwellSpec_pins`
21. `Checked.Sim.Duffing.IsDuffingSolution` · `duffingSpec_pins`
22. `Checked.Sim.MichaelisMenten.IsMMSolution` · `mmSpec_pins`
23. `Checked.Sim.Robertson.IsRobSolution` · `robSpec_pins`

## Output (write exactly one file: `runs/2026-11-08T2228Z/names/NAMES.txt`)
One line per definition, in the order above:

    NAME | <full Lean name> | <name>

- `<name>`: a plain-English noun phrase of 2 to 8 words, lowercase except proper names, Greek letters and
  abbreviations of models, no formula characters (no = + - / * ^ < > ′), no article at the start. For a property
  (a Lean `Prop`), name the law, equation or condition it states (form: `X equation`, `X expansion law`,
  `X condition`), not the sentence. Include every restricting qualifier the specification makes (flat, dust,
  metric F(R), Maxwell, the kind of distance) and nothing the specification does not say.

At the end, a line `END` and a one-paragraph note (after `END`) on anything you could not decide.
