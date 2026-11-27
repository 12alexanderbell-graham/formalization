# Blind specification reading J (sourced reading of three F(R)-cosmology items) — run 2026-11-27T1028Z

You write, from the cited source, Lean 4 **specifications** of one cosmological quantity and two equations:
for each, a `structure … : Prop` whose fields are the laws the source states (or that follow directly from
how the source defines the quantity). Another program has its own definitions and its own specifications of
these; a machine will then try to prove that (1) the other program's definition satisfies your specification
and (2) every function satisfying your specification equals that definition (for an equation: is equivalent
to it) wherever the source's notion is meaningful. You must NOT read the other program's text.

**The source is handed to you.** Verbatim excerpts of the LaTeX source of the paper (as fetched from arXiv,
line numbers of the source file, nothing added) are in the single file
`/home/claude/formalization/runs/2026-11-27T1028Z/sources/bamba2012_1205.3421v3.md`
(Bamba, Capozziello, Nojiri, Odintsov, "Dark energy cosmology: the equivalent description via different
theoretical models and cosmography tests", Astrophys. Space Sci. 2012). Read it in full before writing. The
items concern its section XI ("An example: testing F(R) gravity by cosmography"). Base every field on the
source; where it is silent, say so in the docstring and state the choice you made. Where a convention (a sign,
a normalisation) matters, use the one of section XI as printed, not your memory of other texts. The web is
not available in this session.

**Do not read** anything else under `/home/claude/formalization`: not `Checked`, `Work`, `scripts`,
`_archive`, any other folder of `runs` (only this brief and the one source file named above), and no other
`*.md` / `*.txt` file of the repository. Do not grep or list the repository. Scratch work (Python/sympy)
under `/tmp/specJ/`. To compile, write the file and run
`cd /home/claude/formalization && source ~/.elan/env && lake env lean <file>` (it imports only Mathlib;
another build may be running, so a compile can take a few minutes).

Write exactly one file: `/home/claude/formalization/runs/2026-11-27T1028Z/specJ/SecondReadingSpecJ.lean`
starting with the Mathlib imports you need (never `import Mathlib` as a whole; for example
`Mathlib.Analysis.Calculus.Deriv.Basic`, `Mathlib.Analysis.Calculus.IteratedDeriv.Defs`,
`Mathlib.Analysis.SpecialFunctions.Pow.Real` or whatever the names need), then
`namespace Checked.Trust.SecondReadingSpecJ`, ending with `end Checked.Trust.SecondReadingSpecJ`. It must
compile with no `sorry`, no `axiom`, no new notation or macros. It contains only the three structures (helper
`def`s of your own are allowed if you need them; no theorems are required). Each structure and each field
gets a docstring saying what it states and where in the source (file line numbers) it comes from.

## What a good specification is
- **Faithful:** every field is something the source says (or a direct consequence of its definitions). If a
  field is your own addition, say so in its docstring.
- **Determining:** taken together, the fields should fix the function's value (for an equation: its truth)
  at every argument where the source's notion is meaningful. State those conditions as hypotheses inside the
  fields, and say in the structure's docstring which arguments your specification determines.
- **Not over-determining:** do not constrain values where the source's notion is undefined (for example
  where a quantity the source divides by vanishes).
- For an equation (items 2 and 3) the natural field is an equivalence `P … ↔ (the equation as you read it)`,
  with the side conditions under which you read it.
- Use Mathlib's `deriv`, iterated derivatives (`deriv^[n] f` or `iteratedDeriv n f`), real powers and so on
  as you see fit. Write every derivative of a function of time as a derivative of an explicit Lean function
  of time (so that, for example, the time derivative of a quantity built from `a` is `deriv` of that function).

## Conventions (all three)
Units with the speed of light `c = 1`. `a : ℝ → ℝ` is the scale factor of the **spatially flat** FLRW metric
as a function of cosmic time, **not normalised to one today**; `t₀` is the present time (the time of
observation), `t` the time at which the quantity or equation is evaluated. "Hubble rate" is the expansion rate
of `a` and "Ricci scalar" the curvature scalar of that metric as section XI writes it through the Hubble rate;
spell both out inside your fields (do not define them as separate items; helper `def`s are fine).
`Ω : ℝ` is the present matter density parameter of the source. `F : ℝ → ℝ` is the function F(R) of the
gravity Lagrangian of section XI; primes on F are derivatives with respect to its argument R, dots are
derivatives with respect to cosmic time. The gravitational coupling is as section XI fixes it.

## The three specifications (exact names; the function's type is fixed)

1. `structure DustDensitySpecJ (ρ : ℝ → (ℝ → ℝ) → ℝ → ℝ → ℝ) : Prop` — `ρ Ω a t₀ t` is the matter energy
   density at time `t` in section XI (the matter that, with the curvature fluid, sources the expansion rate),
   in that section's units and coupling, with present matter density parameter `Ω` and present time `t₀`,
   written for a scale factor that is not normalised to one at `t₀`.

2. `structure FRFriedmannSpecJ (P : ℝ → (ℝ → ℝ) → (ℝ → ℝ) → ℝ → ℝ → Prop) : Prop` — `P Ω a F t₀ t` is the
   statement "section XI's Friedmann equation of F(R) gravity (the expansion-rate equation with matter and the
   effective curvature fluid, in the form section XI prints it) holds at time `t`" for the flat scale factor
   `a`, the function `F`, present matter density parameter `Ω` and present time `t₀`.

3. `structure FRMasterSpecJ (P : ℝ → (ℝ → ℝ) → (ℝ → ℝ) → ℝ → ℝ → Prop) : Prop` — `P Ω a F t₀ t` is the
   statement "section XI's master equation for the Hubble parameter holds at time `t`", same arguments.

At the end, reply with: the file path, whether it compiled, which source file you read, and for each item:
which arguments your specification determines, any convention you had to choose (and which source lines
decided it), and anything in the source you found ambiguous, inconsistent or questionable.
