# Blind second formulation D (run 2026-11-05T2028Z)

You write, from your own knowledge and derivation, Lean 4 definitions of seven named quantities.
Another program wrote definitions with the same names; a machine will check (by unfolding and
`ring`/`simp`/`rfl`) whether yours equal theirs. You must NOT read theirs.

**Do not read** anything under `/home/claude/formalization/Checked`, `/home/claude/formalization/Work`,
`/home/claude/formalization/runs` (except this brief), `/home/claude/formalization/scripts`, or any
`*.md` / `*.txt` file of the repository, and do not grep the repository for these names. You MAY
`import` the program modules named below (so that the program's other names, listed with their
meaning, resolve), without opening them. You may use Python/sympy (scratch files under
`/tmp/blindD/`), and Lean: `cd /home/claude/formalization && PATH=$HOME/.elan/bin:$PATH lake env lean /tmp/blindD/X.lean`
(a background build is running; a compile may be slow or report a missing .olean for a module that is
not built yet — then wait a few minutes and retry; never run `lake build` yourself).

Write exactly one file: `/home/claude/formalization/runs/2026-11-05T2028Z/blind_formulation/SecondFormulationD.lean`:
```lean
import Checked.Cosmography.FREta
import Checked.Cosmography.BambaAngular
import Checked.Fidelity.FriedmannLCDM
namespace Checked.Trust.SecondFormulation
open Checked.Cosmography
... your definitions ...
end Checked.Trust.SecondFormulation
```
Each definition gets a docstring saying what it is and how you derived it. No `sorry`. Exact names,
argument orders and types as below. If you cannot derive an item, leave it out and say why.

Program names you may use (their meaning): `hubble a t` = ȧ(t)/a(t); `decel a t₀` = q₀;
`cosmoCoeff 3 a t₀`, `cosmoCoeff 4 a t₀`, `cosmoCoeff 5 a t₀` = j₀, s₀, l₀ (jerk, snap, lerk);
`yred a t₀ t` = y = z/(1+z) of light emitted at t, received at t₀; `angDist K a t₀ t` = angular-diameter
distance (curvature K, c = 1); `omega0 K a t₀` = Ω₀ = 1 + K/(H₀²a₀²);
`Checked.Cosmography.BambaA.DA1 q` and `Checked.Cosmography.BambaA.DA2 q j Ω₀` = the first two
coefficients of the y-series of H₀ d_A; `Checked.Cosmography.FRCosmo.P0 q j s l`, `Q0 q j s l`,
`P2 q j s`, `Q2 q j s`, `P3 q j s l`, `Q3 q j s l` = the quantities 𝒫₀, 𝒬₀, 𝒫₂, 𝒬₂, 𝒫₃, 𝒬₃ of the
source in item 3; `Checked.Cosmography.FREta.qL Ω` and `Checked.Cosmography.FREta.jL` = deceleration
and jerk of flat ΛCDM with matter fraction Ω.

## The seven definitions

1. `def RoundsTo (x d : ℝ) (k : ℕ) : Prop` — "the real number x, rounded to k decimal places, is d":
   x lies within half a unit of the k-th decimal place of d, boundary INCLUDED (≤).

2. `noncomputable def coshBounce : ℝ → ℝ` — the scale factor a(t) of the spatially flat FLRW model
   with H² = 4/9 − (4/9)·a⁻³ (a cosmological constant plus a NEGATIVE-density dust term) that bounces
   at t = 0 with a(0) = 1 and is even in t. Closed form; use `Real.cosh`/`Real.sinh` and real powers
   (`x ^ (p : ℝ)`).

3. Source (Bamba, Capozziello, Nojiri, Odintsov 2012, Sec. XI, F(R) gravity cosmography; conventions:
   κ² = 1, flat FLRW, dust ρ_M = 3H₀²Ω_M a⁻³ with a(t₀) = 1, Ricci scalar R = −6(Ḣ + 2H²), F′(R₀) = 1,
   F⁽⁴⁾(R₀) = 0). The source prints:
   (11.21) F(R₀)/(6H₀²) = −(𝒫₀Ω_M + 𝒬₀)/ℛ,
   (11.23) F″(R₀)/(6H₀²)⁻¹ = −(𝒫₂Ω_M + 𝒬₂)/ℛ,
   (11.24) F‴(R₀)/(6H₀²)⁻² = −(𝒫₃Ω_M + 𝒬₃)/((j₀ − q₀ − 2)ℛ),
   with the same ℛ in all three. Define
   `noncomputable def eta20Of (Ω q j s l : ℝ) : ℝ` = F″(R₀)·H₀⁴/F(R₀), and
   `noncomputable def eta30Of (Ω q j s l : ℝ) : ℝ` = F‴(R₀)·H₀⁶/F(R₀),
   obtained from these printed relations (ℛ cancels), in terms of P0…Q3 (program names above),
   Ω = Ω_M, q = q₀, j = j₀, s = s₀, l = l₀. Write each as a single fraction.

4. `noncomputable def Jfam (Ω ε : ℝ) : ℝ` — the quantity j₀ − q₀ − 2 on the one-parameter family of
   cosmographic parameters obtained by multiplying the flat-ΛCDM values (`qL Ω`, `jL`) by (1 + ε).

5. `noncomputable def remA (D3 : ℝ → ℝ → ℝ → ℝ → ℝ) (D4 : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ) (K : ℝ) (a : ℝ → ℝ) (t₀ t : ℝ) : ℝ`
   — the remainder of H₀·d_A after the y-series through y⁴: H₀ d_A(t) minus y·[1 + 𝒟¹ y + 𝒟² y² + 𝒟³ y³ + 𝒟⁴ y⁴],
   where 𝒟¹ = DA1 q₀, 𝒟² = DA2 q₀ j₀ Ω₀, 𝒟³ = D3 q₀ j₀ s₀ Ω₀, 𝒟⁴ = D4 q₀ j₀ s₀ l₀ Ω₀ (all at t₀), H₀ = hubble a t₀.

6. `noncomputable def correctR (q j s l : ℝ) : ℝ` — the CORRECT denominator ℛ of item 3: derive
   F(R₀), F″(R₀), F‴(R₀) from the field equations of metric F(R) gravity with dust in flat FLRW at t₀
   (source conventions: (11.1)–(11.2) H² = (1/3)[ρ_M/F′(R) + ρ_curv],
   ρ_curv = (1/F′(R))[(F(R) − R F′(R))/2 − 3H Ṙ F″(R)];
   (11.5) Ḣ = −(1/(2F′(R)))[ρ_M + R̈ F″(R) + Ṙ(Ṙ F‴(R) − H F″(R))]; use (11.1) at t₀, (11.5) at t₀ and the
   time derivative of (11.5) at t₀, with F′(R₀) = 1 and F⁽⁴⁾(R₀) = 0; express Ḣ, Ḧ, …, R, Ṙ, R̈, d³R/dt³ at
   t₀ through H₀, q₀, j₀, s₀, l₀ yourself). The three unknowns solve a linear system; ℛ is (up to
   normalisation) its determinant divided by H₀-powers. Normalisation: the coefficient of l₀ in ℛ is
   exactly (j₀ − q₀ − 2). Report also, in your final message, your F(R₀)/(6H₀²) numerator so we can
   compare signs.

At the end, reply with the file path, each item's formula in plain text, and any item where you were
unsure of the convention.
