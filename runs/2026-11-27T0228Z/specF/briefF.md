# Blind specification reading F (chemistry, simulation and one cosmography definition) — run 2026-11-27T0228Z

You write, from the cited sources and your own knowledge, Lean 4 **specifications** of six notions: for
each, a `structure … : Prop` whose fields state what the source means by the notion. Another program has
its own definitions and specifications of these; a machine will then try to prove that (1) the other
program's definition satisfies your specification and (2) every predicate (or function) satisfying your
specification is equivalent (equal) to that definition. You must NOT read the other program's text.

**Do not read** anything under `/home/claude/formalization/Checked`, `/home/claude/formalization/Work`,
`/home/claude/formalization/runs` (except this brief), `/home/claude/formalization/scripts`,
`/home/claude/formalization/_archive`, or any `*.md` / `*.txt` file of the repository. Do not grep the
repository. Web access is normally refused in this session; write from your knowledge of the sources and
say so. Scratch work under `/tmp/specF/`. To compile, write the file and run
`cd /home/claude/formalization && source ~/.elan/env && lake env lean <file>` (it imports only Mathlib).

Write exactly one file: `/home/claude/formalization/runs/2026-11-27T0228Z/specF/SecondReadingSpecF.lean`
starting with the Mathlib imports you need (never `import Mathlib` as a whole; for example
`Mathlib.Analysis.Calculus.Deriv.Basic`, `Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic`), then
`namespace Checked.Trust.SecondReadingSpecF`, ending with `end Checked.Trust.SecondReadingSpecF`. It must
compile with no `sorry`, no `axiom`, no new notation or macros. It contains only the six structures (helper
`def`s of your own are allowed; no theorems required). Each structure and field gets a docstring saying
what it states and where in the source it comes from.

## What a good specification is
- **Faithful:** every field is what the source says the notion means. If a field is your own addition
  (a regularity or ordering condition the source leaves implicit), say so in its docstring.
- **Determining:** for a predicate (items 1–5) the natural field is an equivalence `P … ↔ (your reading)`,
  for every argument; for the function of item 6 a defining formula under stated conditions.
- Be explicit about what the source leaves to the reader: which derivatives are meant at the ends of a time
  interval, which regularity a solution has, whether volumes are ordered, and so on; choose, and say what
  you chose.

## The six specifications (exact names; the types are fixed)

1. `structure CriticalSpecF (P : (ℝ → ℝ) → ℝ → Prop) : Prop` — `P p v` says: the molar volume `v` is
   the critical point of the isotherm `p` (pressure as a function of molar volume at one temperature), in the
   sense of the conditions by which the critical temperature and volume of a cubic equation of state such as
   van der Waals' are found (e.g. Poling, Prausnitz and O'Connell, *The Properties of Gases and Liquids*,
   ch. 4; any thermodynamics textbook's van der Waals critical point).

2. `structure CoexistenceSpecF (P : (ℝ → ℝ) → ℝ → ℝ → ℝ → Prop) : Prop` — `P p vl vg ps` says: the
   liquid volume `vl`, the gas volume `vg` and the saturation pressure `ps` are a vapour–liquid coexistence
   state of the isotherm `p` by Maxwell's equal-area construction (e.g. Callen, *Thermodynamics*, ch. 9).

3. `structure DuffingSpecF (P : ℝ → ℝ → ℝ → ℝ → ℝ → (ℝ → ℝ) → Prop) : Prop` — `P k β x₀ v₀ T x` says:
   `x` is a solution on the time interval `[0, T]` of the undamped, unforced Duffing oscillator with linear
   stiffness `k` and cubic stiffness `β` (unit mass), with initial position `x₀` and initial velocity `v₀`
   (Kovacic and Brennan, *The Duffing Equation*, 2011, ch. 1).

4. `structure MMSpecF (P : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → (ℝ → ℝ) → (ℝ → ℝ) → (ℝ → ℝ) → (ℝ → ℝ) → Prop) : Prop`
   — `P k₁ km₁ k₂ s₀ e₀ c₀ p₀ T s e c p` says: the concentrations `s` (substrate), `e` (free enzyme), `c`
   (enzyme–substrate complex) and `p` (product) solve on `[0, T]` the mass-action rate equations of the full
   Michaelis–Menten mechanism E + S ⇌ C → E + P, with binding rate constant `k₁`, unbinding rate constant
   `km₁` and catalytic rate constant `k₂`, starting from `s₀, e₀, c₀, p₀` at time 0 (Segel and Slemrod 1989,
   SIAM Review 31, 446).

5. `structure RobSpecF (P : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → (ℝ → ℝ) → (ℝ → ℝ) → (ℝ → ℝ) → Prop) : Prop` —
   `P k₁ k₂ k₃ a₀ b₀ c₀ T y₁ y₂ y₃` says: the concentrations `y₁ = [A]`, `y₂ = [B]`, `y₃ = [C]` solve on
   `[0, T]` the mass-action rate equations of Robertson's (1966) reaction network, numbered here as
   A → B (rate constant `k₁`), B + C → A + C (rate constant `k₂`), 2B → B + C (rate constant `k₃`), starting
   from `a₀, b₀, c₀` at time 0 (Robertson 1966; Hairer and Wanner, *Solving ODEs II*, §IV.1 — mind that the
   numbering of the constants here is fixed as stated, whatever a book's numbering).

6. `structure ComovingSpecF (X : (ℝ → ℝ) → ℝ → ℝ → ℝ) : Prop` — `X a t₀ t` is the comoving radial
   (line-of-sight) coordinate distance travelled by light emitted at time `t` and observed at `t₀` in an FLRW
   model with scale factor `a` (not normalised to one today), units with `c = 1` (Hogg 1999,
   astro-ph/9905116, §5; Weinberg, *Cosmology*, §1.4). Positive continuous scale factor on the light's path.

At the end, reply with: the file path, whether it compiled, which sources you opened (if any), and for each
item: what you chose where the source leaves a choice (end-point derivatives, regularity, ordering), and
anything you found ambiguous.
