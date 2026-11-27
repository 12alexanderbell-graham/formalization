# Blind specification reading H (sourced re-reading of four cosmology definitions) — run 2026-11-27T0428Z

You write, from the cited sources, Lean 4 **specifications** of four cosmological quantities and model
conditions: for each, a `structure … : Prop` whose fields are the laws the source states (or that follow
directly from how the source defines the quantity). Another program has its own definitions and its own
specifications of these; a machine will then try to prove that (1) the other program's definition satisfies
your specification and (2) every function satisfying your specification equals that definition (for a
condition: is equivalent to it) wherever the source's notion is meaningful. You must NOT read the other
program's text.

**The sources are handed to you.** Verbatim excerpts of the LaTeX sources of the three papers (as fetched
from arXiv, line numbers of the source file, nothing added) are in
`/home/claude/formalization/runs/2026-11-27T0428Z/sources/`:
`bamba2012_1205.3421v3.md`, `aviles2012_1204.2007.md`, `capozziello2011_1104.3096.md`. Read all three
files in full before writing. Base every field on them; where they are silent, say so in the docstring and
state the choice you made. Several items depend on a convention of a named section of a source (a sign); use
that section's convention, not your memory of other texts. The web is not available in this session.

**Do not read** anything else under `/home/claude/formalization`: not `Checked`, `Work`, `scripts`,
`_archive`, any other folder of `runs` (only this brief and the `sources/` folder named above), and no
other `*.md` / `*.txt` file of the repository. Do not grep the repository. Scratch work (Python/sympy) under
`/tmp/specH/`. To compile, write the file and run
`cd /home/claude/formalization && source ~/.elan/env && lake env lean <file>` (it imports only Mathlib;
another build may be running, so a compile can take a few minutes).

Write exactly one file: `/home/claude/formalization/runs/2026-11-27T0428Z/specH/SecondReadingSpecH.lean`
starting with the Mathlib imports you need (never `import Mathlib` as a whole; for example
`Mathlib.Analysis.Calculus.Deriv.Basic`, `Mathlib.Analysis.SpecialFunctions.Sqrt`,
`Mathlib.Analysis.SpecialFunctions.Pow.Real`, `Mathlib.Analysis.SpecialFunctions.Exp`,
`Mathlib.Order.Filter.Basic`, `Mathlib.Topology.Basic` or whatever the names need), then
`namespace Checked.Trust.SecondReadingSpecH`, ending with `end Checked.Trust.SecondReadingSpecH`. It must
compile with no `sorry`, no `axiom`, no new notation or macros. It contains only the four structures (helper
`def`s of your own are allowed if you need them; no theorems are required). Each structure and each field
gets a docstring saying what it states and where in the source (file line numbers) it comes from.

## What a good specification is
- **Faithful:** every field is something the source says (or a direct consequence of its definition): a
  defining formula, a defining differential relation, a value on a standard model. If a field is your own
  addition, say so in its docstring.
- **Determining:** taken together, the fields should fix the function's value (for a condition: its truth)
  at every argument where the source's notion is meaningful. State those conditions as hypotheses inside the
  fields, and say in the structure's docstring which arguments your specification determines.
- **Not over-determining:** do not constrain values where the source's notion is undefined.
- For a model condition (items 3 and 4) the natural field is an equivalence `P … ↔ (your reading)`; state
  exactly where (all times, or near the observation time) and with which side conditions the source's model
  sentence holds, as you read it, and say in the docstring which words of the source decided it.
- Use Mathlib's `deriv`, `HasDerivAt`, `Real.sqrt`, `Real.exp`, real powers `x ^ (r : ℝ)` and filters
  (`∀ᶠ s in nhds t₀, …`) as you see fit.

## Conventions (all four)
Units with the speed of light `c = 1`. `a : ℝ → ℝ` is the FLRW scale factor as a function of cosmic time
(not normalised to one today); `t₀` is the time of observation, `t` the time of emission of light
(`t ≤ t₀` for light received at `t₀`). `K : ℝ` is the curvature constant of the metric
`ds² = −dt² + a(t)² (dr²/(1 − K r²) + r² dΩ²)` (not normalised to −1, 0, 1). "Redshift" is the
cosmological redshift between `t` and `t₀`; "Hubble rate" is the expansion rate of `a`; spell both out
inside your fields (do not define them as separate items).

## The four specifications (exact names; the function's type is fixed)

1. `structure CurvParamSpecH (k : ℝ → (ℝ → ℝ) → ℝ → ℝ) : Prop` — `k K a t₀` is the dimensionless spatial
   curvature parameter that appears in the cosmographic expansions of the distances with curvature in
   Bamba et al. 2012 §X, written through `K`, `a(t₀)` and the Hubble rate at `t₀`, in that section's sign
   convention.

2. `structure RicciFlatSpecH (R : (ℝ → ℝ) → ℝ → ℝ) : Prop` — `R a t` is the Ricci scalar of the spatially
   flat FLRW metric with scale factor `a` at time `t`, **as Bamba et al. 2012 §XI uses it** (their
   cosmographic test of F(R) gravity, printed equation (11.6) and around), written through the Hubble rate and
   its time derivative or through `a` and its derivatives. If the source uses different conventions in
   different sections, say so in the docstring and follow §XI.

3. `structure FlatLCDMSpecH (P : ℝ → (ℝ → ℝ) → ℝ → Prop) : Prop` — `P Ω a t₀` is the condition "the scale
   factor `a` is that of a spatially flat ΛCDM universe (dust and a cosmological constant, no radiation)
   with present matter density parameter `Ω`, the present being `t₀`", as Aviles, Gruber, Luongo and
   Quevedo 2012 state their flat ΛCDM model in terms of the expansion rate as a function of redshift.

4. `structure FlatCPLSpecH (P : ℝ → ℝ → ℝ → (ℝ → ℝ) → ℝ → Prop) : Prop` — `P Ω w₀ wₐ a t₀` is the
   condition "the scale factor `a` is that of a spatially flat universe of dust and a dark energy with the
   Chevallier–Polarski–Linder equation of state, present matter density parameter `Ω`, the present being
   `t₀`", as Capozziello, Lazkoz and Salzano 2011 state it through the expansion rate as a function of
   redshift.

At the end, reply with: the file path, whether it compiled, which source files you read, and for each item:
which arguments your specification determines, any convention you had to choose (and which source lines
decided it), and anything in the sources you found ambiguous, inconsistent or questionable.
