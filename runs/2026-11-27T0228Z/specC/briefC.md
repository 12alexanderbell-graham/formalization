# Blind specification reading C (cosmography definitions, second batch) — run 2026-11-27T0228Z

You write, from the cited sources and your own knowledge, Lean 4 **specifications** of seven
cosmological quantities and model conditions: for each, a `structure … : Prop` whose fields are the laws
the source states (or that follow directly from how the source defines the quantity). Another program has
its own definitions and its own specifications of these; a machine will then try to prove that (1) the
other program's definition satisfies your specification and (2) every function satisfying your
specification equals that definition (for a condition: is equivalent to it) wherever the source's notion
is meaningful. You must NOT read the other program's text.

**Do not read** anything under `/home/claude/formalization/Checked`, `/home/claude/formalization/Work`,
`/home/claude/formalization/runs` (except this brief), `/home/claude/formalization/scripts`,
`/home/claude/formalization/_archive`, or any `*.md` / `*.txt` file of the repository. Do not grep the
repository. **Read the sources themselves if your tools allow it** (arXiv abstract pages and PDFs, for
example `https://arxiv.org/abs/1205.3421`); several items depend on a convention of a named source
(a sign, a normalisation), and memory of other textbooks is not enough there. Say in your reply which
sources you actually opened. Scratch work (Python/sympy) under `/tmp/specC/`. To compile, write the file
and run `cd /home/claude/formalization && source ~/.elan/env && lake env lean <file>` (it imports only
Mathlib; another build may be running, so a compile can take a few minutes).

Write exactly one file: `/home/claude/formalization/runs/2026-11-27T0228Z/specC/SecondReadingSpecC.lean`
starting with the Mathlib imports you need (never `import Mathlib` as a whole; for example
`Mathlib.Analysis.Calculus.Deriv.Basic`, `Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic`,
`Mathlib.Analysis.SpecialFunctions.Sqrt`, `Mathlib.Analysis.SpecialFunctions.Pow.Real`,
`Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic`, `Mathlib.Order.Filter.Basic`,
`Mathlib.Topology.Basic` or whatever the names need), then `namespace Checked.Trust.SecondReadingSpecC`,
ending with `end Checked.Trust.SecondReadingSpecC`. It must compile with no `sorry`, no `axiom`, no new
notation or macros. It contains only the seven structures (helper `def`s of your own are allowed if you
need them; no theorems are required). Each structure and each field gets a docstring saying what it
states and where in the source it comes from.

## What a good specification is
- **Faithful:** every field is something the source says (or a direct consequence of its definition):
  a defining formula, a defining differential relation, a value on a standard model, a symmetry. If a
  field is your own addition, say so in its docstring.
- **Determining:** taken together, the fields should fix the function's value (for a condition: its truth)
  at every argument where the source's notion is meaningful. State those conditions as hypotheses inside
  the fields, and say in the structure's docstring which arguments your specification determines.
- **Not over-determining:** do not constrain values where the source's notion is undefined.
- For a model condition (items 4 and 5) the natural field is an equivalence `P … ↔ (your reading)`;
  state exactly where (all times, or near the observation time) and with which side conditions the
  source's model sentence holds, as you read it.
- Use Mathlib's `deriv`, `HasDerivAt`, `Real.sqrt`, `Real.sin`, `Real.sinh`, `Real.exp`, real powers
  `x ^ (r : ℝ)`, interval integrals `∫ s in t..t₀, f s`, and filters (`∀ᶠ s in nhds t₀, …`) as you see fit.

## Conventions (all seven)
Units with the speed of light `c = 1`. `a : ℝ → ℝ` is the FLRW scale factor as a function of cosmic
time (not normalised to one today); `t₀` is the time of observation, `t` the time of emission of the
light (`t ≤ t₀` for light received at `t₀`). `K : ℝ` is the curvature constant of the metric
`ds² = −dt² + a(t)² (dr²/(1 − K r²) + r² dΩ²)` (not normalised to −1, 0, 1); a closed universe has
`K > 0`. "Redshift" is the cosmological redshift between `t` and `t₀`; "Hubble rate" is the expansion
rate of `a`; spell both out inside your fields (do not define them as separate items).

## The seven specifications (exact names; the function's type is fixed)

1. `structure TransverseSpecC (S : ℝ → ℝ → ℝ) : Prop` — `S K χ` is the FLRW transverse (angular)
   comoving distance function of a comoving radial distance `χ` for curvature constant `K` (the function
   that is a sine for closed, the identity for flat and a hyperbolic sine for open models; Hogg 1999,
   astro-ph/9905116, §5, written with `K` instead of `Ω_k`).

2. `structure LumDistSpecC (D : ℝ → (ℝ → ℝ) → ℝ → ℝ → ℝ) : Prop` — `D K a t₀ t` is the
   luminosity distance, in an FLRW model with curvature constant `K` and scale factor `a`, of a source whose
   light was emitted at `t` and is observed at `t₀` (Bamba, Capozziello, Nojiri, Odintsov 2012,
   arXiv:1205.3421, §10; Hogg 1999 §7; Weinberg, *Cosmology*, §1.4). Positive continuous scale factor on
   the light's path. Do not refer to item 1 (spell the function out).

3. `structure AngDistSpecC (D : ℝ → (ℝ → ℝ) → ℝ → ℝ → ℝ) : Prop` — `D K a t₀ t` is the
   angular diameter distance for the same data as item 2 (Hogg 1999 §6; Bamba et al. 2012 §10).

4. `structure FlatLCDMSpecC (P : ℝ → (ℝ → ℝ) → ℝ → Prop) : Prop` — `P Ω a t₀` is the condition
   "the scale factor `a` is that of a spatially flat ΛCDM universe (dust and a cosmological constant, no
   radiation) with present matter density parameter `Ω`, the present being `t₀`", as Aviles, Gruber,
   Luongo and Quevedo 2012 (arXiv:1204.2007) state their flat ΛCDM model (text before their Eq. (15)) in
   terms of the expansion rate as a function of redshift.

5. `structure FlatCPLSpecC (P : ℝ → ℝ → ℝ → (ℝ → ℝ) → ℝ → Prop) : Prop` — `P Ω w₀ wₐ a t₀` is the
   condition "the scale factor `a` is that of a spatially flat universe of dust and a dark energy with the
   Chevallier–Polarski–Linder equation of state `w(z) = w₀ + wₐ z/(1+z)`, present matter density parameter
   `Ω`, the present being `t₀`", as Capozziello, Lazkoz and Salzano 2011 ("Cosmographic analysis of
   dark energy", arXiv:1104.3096, Eq. (17)) state it through the expansion rate as a function of redshift.

6. `structure CurvParamSpecC (k : ℝ → (ℝ → ℝ) → ℝ → ℝ) : Prop` — `k K a t₀` is the dimensionless
   spatial curvature parameter that appears in the cosmographic expansions of the luminosity distance with
   curvature in Bamba et al. 2012 §10, written through `K`, `a(t₀)` and the Hubble rate at `t₀`, **in that
   source's sign convention** (read it there).

7. `structure RicciFlatSpecC (R : (ℝ → ℝ) → ℝ → ℝ) : Prop` — `R a t` is the Ricci scalar of the spatially
   flat FLRW metric with scale factor `a` at time `t`, **in the sign convention of Bamba et al. 2012 §11**
   (their F(R) gravity section, Eq. (11.6) and around; read it there), written through the Hubble rate and
   its time derivative or through `a` and its derivatives.

At the end, reply with: the file path, whether it compiled, which sources you actually opened (and
which items you had to write from memory), and for each item: which arguments your specification
determines, any convention you had to choose, and anything in the sources you found ambiguous or
questionable.
