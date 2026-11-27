# Blind specification reading B (cosmography definitions) — run 2026-11-27T0228Z

You write, from the cited sources and your own knowledge, Lean 4 **specifications** of seven
cosmological quantities: for each, a `structure … : Prop` whose fields are the laws the source states
(or that follow directly from how the source defines the quantity). Another program has its own
definitions and its own specifications of these quantities; a machine will then try to prove that
(1) the other program's definition satisfies your specification and (2) every function satisfying
your specification equals that definition wherever the quantity is meaningful. You must NOT read
the other program's text.

**Do not read** anything under `/home/claude/formalization/Checked`, `/home/claude/formalization/Work`,
`/home/claude/formalization/runs` (except this brief), `/home/claude/formalization/scripts`,
`/home/claude/formalization/_archive`, or any `*.md` / `*.txt` file of the repository. Do not grep the
repository. You may read the sources on the web (arXiv abstract or PDF pages) if your tools allow, and
use Python/sympy for scratch work under `/tmp/specB/`. To compile, write the file and run
`cd /home/claude/formalization && source ~/.elan/env && lake env lean <file>` (it imports only Mathlib;
another build may be running, so a compile can take a few minutes).

Write exactly one file: `/home/claude/formalization/runs/2026-11-27T0228Z/specB/SecondReadingSpecB.lean`
starting with the Mathlib imports you need (never `import Mathlib` as a whole; for example
`Mathlib.Analysis.Calculus.Deriv.Basic`, `Mathlib.Analysis.Calculus.IteratedDeriv.Defs`,
`Mathlib.Analysis.SpecialFunctions.Log.Deriv`, `Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic`
or whatever the names need), then `namespace Checked.Trust.SecondReadingSpecB`, ending with
`end Checked.Trust.SecondReadingSpecB`. It must compile with no `sorry`, no `axiom`, no new notation
or macros. It contains only the seven structures (helper `def`s of your own are allowed if you need
them; no theorems are required). Each structure and each field gets a docstring saying what it states
and where in the source it comes from.

## What a good specification is
- **Faithful:** every field is something the source says (or a direct consequence of its definition):
  a defining formula, a defining differential relation, a value on a standard model, a symmetry. If a
  field is your own addition, say so in its docstring.
- **Determining:** taken together, the fields should fix the function's value at every argument where
  the source's quantity is meaningful (for example: positive scale factor, enough derivatives,
  denominators nonzero). State those conditions as hypotheses inside the fields, and say in the
  structure's docstring which arguments your specification determines.
- **Not over-determining:** do not constrain values where the source's quantity is undefined (a zero
  scale factor, a non-differentiable function), so that any reasonable convention there still meets
  your specification.
- Use Mathlib's `deriv`, `HasDerivAt`, `iteratedDeriv`, `Real.log`, `Real.exp`, interval integrals
  `∫ s in t..t₀, f s` as you see fit; real powers `x ^ (r : ℝ)` are `Real.rpow`.

## Conventions (all seven)
Units with the speed of light `c = 1`. `a : ℝ → ℝ` is the FLRW scale factor as a function of cosmic
time (not normalised to one today); `t₀` is the time of observation, `t` the time of emission of the
light (`t ≤ t₀` for light received at `t₀`). `K : ℝ` is the curvature constant of the metric
`ds² = −dt² + a(t)² (dr²/(1 − K r²) + r² dΩ²)` (not normalised to −1, 0, 1).

## The seven specifications (exact names; the function's type is fixed)

1. `structure HubbleSpecB (H : (ℝ → ℝ) → ℝ → ℝ) : Prop` — `H a t` is the Hubble expansion rate of
   the scale factor `a` at cosmic time `t` (Weinberg, *Cosmology*, §1.5; Hogg 1999, astro-ph/9905116, §3).

2. `structure DecelSpecB (Q : (ℝ → ℝ) → ℝ → ℝ) : Prop` — `Q a t` is the deceleration parameter
   at cosmic time `t` (Weinberg §1.5; Visser 2004, "Jerk, snap and the cosmological equation of
   state", gr-qc/0309109).

3. `structure RedshiftSpecB (Z : (ℝ → ℝ) → ℝ → ℝ → ℝ) : Prop` — `Z a t₀ t` is the cosmological
   redshift `z` of light emitted at time `t` and observed at time `t₀` (Weinberg §1.2; Hogg 1999 §2).

4. `structure CoeffSpecB (C : ℕ → (ℝ → ℝ) → ℝ → ℝ) : Prop` — `C n a t` is the `n`-th
   cosmographic coefficient at time `t` in the sense of Aviles, Gruber, Luongo and Quevedo 2012
   ("Cosmography and constraints on the equation of state of the Universe in various
   parametrizations", arXiv:1204.2007, Eq. (3)), where the jerk, snap, lerk and the next coefficient
   are the values at `n = 3, 4, 5, 6`. The source defines a pattern; specify it for general `n` if the
   pattern defines it, and say for which `n` your fields determine `C`. Write it without referring to
   your item 1 (spell out the expansion rate inside the fields if you need it).

5. `structure YRedSpecB (Y : (ℝ → ℝ) → ℝ → ℝ → ℝ) : Prop` — `Y a t₀ t` is the "y-redshift"
   `y` of Cattoën and Visser (2007, gr-qc/0703122, "The Hubble series: convergence properties and
   redshift variables") as used in Bamba, Capozziello, Nojiri and Odintsov 2012 (arXiv:1205.3421,
   §10), for the same emission and observation times as item 3. Spell out the redshift inside the
   fields if you need it (do not refer to item 3).

6. `structure Omega0SpecB (O : ℝ → (ℝ → ℝ) → ℝ → ℝ) : Prop` — `O K a t₀` is the present total
   density parameter `Ω₀` of the FLRW model, written through the Friedmann equation in terms of the
   curvature constant `K`, the scale factor and its expansion rate at `t₀` (Bamba et al. 2012 §10; the
   model's total density is whatever makes the Friedmann equation hold).

7. `structure LumDistFlatSpecB (D : (ℝ → ℝ) → ℝ → ℝ → ℝ) : Prop` — `D a t₀ t` is the luminosity
   distance, in a spatially flat FLRW model (`K = 0`) with scale factor `a`, of a source whose light was
   emitted at `t` and is observed at `t₀` (Hogg 1999 §7; Weinberg §1.4; Bamba et al. 2012 §10).
   Positive continuous scale factor on the light's path.

At the end, reply with: the file path, whether it compiled, and for each item: which arguments your
specification determines, any convention you had to choose (sign, normalisation, range of `n`), and
anything in the sources you found ambiguous or questionable.
