import Mathlib

/-!
# Reader C reading of the quasi-Riemann hypothesis manuscripts (target O)

Sources read: `sources/paper_sep30_lines.tex` (paper.tex, 30 Sep 2026) and
`sources/paper2_oct5_lines.tex` (paper2.tex, 5 Oct 2026). Only the brief and these
two excerpts were used. See the comment block at the end for ambiguities and for
the differences between the two headline claims.
-/

noncomputable section

open Ideal

namespace QRHReadingC

/-- The field `Q(√-3)`, modelled as `ℚ(ζ₃)`. -/
abbrev QK : Type := CyclotomicField 3 ℚ

/-- Its ring of integers `𝓞 = O_K`. -/
abbrev OK : Type := NumberField.RingOfIntegers QK

/-- A finite-order Hecke character of modulus `f` (a nonzero integral ideal), viewed as a
function on integral ideals, extended by zero to ideals not coprime to `f`
(coprime means `I ⊔ f = ⊤`, i.e. `I + f = 𝓞`).

It is a character of the ray class group mod `f`, in the following sense:
* it vanishes on ideals not coprime to `f`, and `η (𝓞) = 1`;
* it is multiplicative (on all integral ideals; the non-coprime case is automatic);
* it is trivial on principal ideals `(α)` with `α ≡ 1 mod^× f`. Such an `α` is written
  `a / b` with `a, b ∈ 𝓞` nonzero, coprime to `f`, and `a - b ∈ f`. The relation
  `(α) J = I` between integral ideals `I, J` coprime to `f` reads `(b) I = (a) J`, and
  then `η I = η J`. This is the statement that `η` factors through
  `I ↦ I J⁻¹`, i.e. through the ray class group;
* it has finite order: some `n ≥ 1` has `η I ^ n = 1` for all coprime `I`. -/
structure IsHeckeChar (f : Ideal OK) (η : Ideal OK → ℂ) : Prop where
  zero_of_not_coprime : ∀ I : Ideal OK, I ⊔ f ≠ ⊤ → η I = 0
  map_top : η ⊤ = 1
  mul : ∀ I J : Ideal OK, η (I * J) = η I * η J
  ray_trivial : ∀ (I J : Ideal OK) (a b : OK), I ⊔ f = ⊤ → J ⊔ f = ⊤ →
    a ≠ 0 → b ≠ 0 → Ideal.span {a} ⊔ f = ⊤ → Ideal.span {b} ⊔ f = ⊤ → a - b ∈ f →
    Ideal.span {b} * I = Ideal.span {a} * J → η I = η J
  finite_order : ∃ n : ℕ, 0 < n ∧ ∀ I : Ideal OK, I ⊔ f = ⊤ → η I ^ n = 1

/-- `η` is principal (the trivial character mod `f`): it is `1` on every ideal coprime to `f`.
Only for principal `η` does the manuscript allow a pole at `s = 1`. -/
def IsPrincipalHecke (f : Ideal OK) (η : Ideal OK → ℂ) : Prop :=
  ∀ I : Ideal OK, I ⊔ f = ⊤ → η I = 1

/-- Reading of "ζ(s) has no zero in Re s > σ₀". Mathlib's `riemannZeta` is defined on all of
ℂ. Its only pole is at `s = 1`, which is excluded from the statement (the manuscript allows
the pole there). -/
def ReadingZeta (σ₀ : ℝ) : Prop :=
  ∀ s : ℂ, σ₀ < s.re → s ≠ 1 → riemannZeta s ≠ 0

/-- Reading of "every Dirichlet L-function has no zero in Re s > σ₀", over all characters
modulo every `N ≥ 1`, including imprimitive ones (the Sep 30 convention). The character modulo 1
is the trivial one, whose `LFunction` is `ζ`.
The pole at `s = 1` is excluded only for the principal (trivial) character `χ = 1`, where
`DirichletCharacter.LFunction` is a junk value at the pole. For nonprincipal `χ` the value at
`s = 1` is the genuine value of a holomorphic function, and the claim is made there too. -/
def ReadingDirichlet (σ₀ : ℝ) : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
    σ₀ < s.re → (s = 1 → χ ≠ 1) → DirichletCharacter.LFunction χ s ≠ 0

/-- Same as `ReadingDirichlet`, but restricted to primitive characters, as in the Oct 5 text
(`For a primitive Dirichlet character χ of conductor q`). Primitive means
`DirichletCharacter.IsPrimitive χ`, i.e. the conductor equals the modulus. -/
def ReadingDirichletPrim (σ₀ : ℝ) : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
    DirichletCharacter.IsPrimitive χ → σ₀ < s.re → (s = 1 → χ ≠ 1) →
      DirichletCharacter.LFunction χ s ≠ 0

/-- Reading of "every finite-order Hecke L-function over Q(√-3) has no zero in Re s > σ₀".

Quantification: over every nonzero modulus `f`, every finite-order Hecke character `η` of
modulus `f`, and every `L : ℂ → ℂ` that
* is holomorphic on `ℂ ∖ {1}`;
* is continuous at `1` when `η` is nonprincipal, so `L` is entire there (the pole at `1` is
  allowed only for principal `η`);
* equals `∑_{𝔞 ≠ 0} η(𝔞) N𝔞^{-s}` for `Re s > 1` (`HasSum` over nonzero integral ideals, which
  asserts convergence as well as the value).
Conclusion: `L s ≠ 0` for `Re s > σ₀`, with `s = 1` included exactly when `η` is nonprincipal.

Holomorphy on `ℂ ∖ {1}` and the Dirichlet series determine `L` uniquely on `ℂ ∖ {1}`
(connected open set, identity theorem), so `L` is the manuscript's continuation. -/
def ReadingHecke (σ₀ : ℝ) : Prop :=
  ∀ (f : Ideal OK), f ≠ ⊥ → ∀ η : Ideal OK → ℂ, IsHeckeChar f η →
    ∀ L : ℂ → ℂ, DifferentiableOn ℂ L ({1}ᶜ : Set ℂ) →
      (¬ IsPrincipalHecke f η → ContinuousAt L 1) →
      (∀ s : ℂ, 1 < s.re →
        HasSum (fun I : {I : Ideal OK // I ≠ ⊥} =>
            η I.1 * ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)) (L s)) →
      ∀ s : ℂ, σ₀ < s.re → (s = 1 → ¬ IsPrincipalHecke f η) → L s ≠ 0

/-- Sep 30 headline claim: Hecke (all finite-order characters), Dirichlet (all characters),
and ζ, all with σ₀ = 7/8. -/
theorem reading_sep30 : ReadingHecke (7/8) ∧ ReadingDirichlet (7/8) ∧ ReadingZeta (7/8) := sorry

/-- Oct 5 headline claim: Hecke, primitive Dirichlet characters, and ζ, with σ₀ = 11/12. -/
theorem reading_oct5 :
    ReadingHecke (11/12) ∧ ReadingDirichletPrim (11/12) ∧ ReadingZeta (11/12) := sorry

end QRHReadingC

/-!
## Ambiguity notes and choices

1. **ζ and the pole.** `riemannZeta` is total on ℂ, but its value at `s = 1` is junk. The
   statement excludes `s = 1` (the manuscripts allow the pole there), so the junk value is
   never used.

2. **Dirichlet characters, all vs primitive.** Sep 30 (`For a Dirichlet character χ modulo q`)
   means every character modulo every `q`, including imprimitive ones. This is
   `ReadingDirichlet`. Oct 5 (`For a primitive Dirichlet character χ of conductor q`) restricts
   to primitive characters. This is `ReadingDirichletPrim`. The two sets differ by imprimitive
   characters, whose `L`-functions differ from primitive ones by finitely many Euler factors
   `∏ (1 - χ*(p) p^{-s})`. Those factors vanish only on `Re s = 0`, so the difference does not
   matter for half-planes with σ₀ ≥ 0. It is still a literal difference in the claim.
   Mathlib's `DirichletCharacter.IsPrimitive` is conductor = level.
   `N` ranges over `N ≥ 1` (`[NeZero N]`); `N = 0` is excluded.

3. **Pole convention for Dirichlet.** `DirichletCharacter.LFunction` is a genuine function with
   a pole at `s = 1` only for the principal character `χ = 1` (as an element of
   `DirichletCharacter ℂ N`). The statement excludes `s = 1` only when `χ = 1`, so for
   nonprincipal `χ` the claim includes `s = 1`. Imprimitive principal characters (`χ = 1` at level
   `N > 1`) are principal and are excluded at `s = 1` too.

4. **Hecke L-functions: no Mathlib model.** Mathlib has no Hecke L-functions over number
   fields, so the continuation is not defined. We quantify over every `L` satisfying the
   properties in the brief. The function `L` is determined on `ℂ ∖ {1}` by the series (identity
   theorem, since `ℂ ∖ {1}` is connected). The value `L 1` is not determined by holomorphy alone.
   So:
   - for principal `η` the pole at `1` is allowed, and `s = 1` is excluded from the conclusion;
   - for nonprincipal `η` the manuscripts' claim includes `s = 1`, which needs `L 1` to be the
     genuine value. This reading adds `ContinuousAt L 1` for nonprincipal `η` and keeps `s = 1`
     in the conclusion. This is a refinement of the brief's `s ≠ 1` rule: the brief excludes `s = 1`
     for all `η`, and this version excludes it only where the pole is allowed.
   Entireness of nonprincipal Hecke `L`-functions is a theorem not used in the statement, so
   `ContinuousAt` is only a hypothesis on the class of `L`.

5. **Vacuity.** `ReadingHecke` is vacuous for any `η` for which no `L` satisfying the hypotheses
   exists. Existence of the continuation is a theorem, not part of the reading.

6. **Ray class group.** Mathlib has no ray class group, so I did not build the quotient. The
   character condition is stated on integral ideals (`IsHeckeChar`). Identifying `η` with a
   homomorphism from `I ↦ I J⁻¹` on coprime fractional ideals gives the quotient by
   `P_{f,1} = {(α) : α ≡ 1 mod^× f}`, using `I = (a/b) J ⇔ bI = aJ`.
   The congruence `α ≡ 1 mod^× f` is the standard `α = a/b` with `a, b` coprime to `f`, `a ≡ b mod f`
   (the representation is quantified over in `ray_trivial`). I require `a, b ≠ 0`, so that `α ≠ 0`
   (otherwise `0/0 = 0` makes every ideal relation hold when `f = 1`).
   `finite_order` is automatic for a character of a finite group, but is stated explicitly.

7. **Ideal-theoretic vs idelic Hecke characters.** The manuscript defines `η` ideal-theoretically
   and says this agrees with the idelic definition, because the complex place contributes no
   nontrivial finite-order continuous character (Milne, Ch. VI §1). I follow the ideal-theoretic
   definition only.

8. **The sum.** The sum is over nonzero integral ideals (`{I // I ≠ ⊥}`). `absNorm ⊥ = 0` is
   avoided by excluding `⊥`. `(N𝔞 : ℂ)^(-s)` is `cpow` with positive real base, so it is
   well-defined. Convergence for `Re s > 1` is part of the statement (`HasSum`), not assumed.

9. **Quantifying over moduli.** Every nonzero `f` (including `f = 1`, the trivial modulus) and
   every `η` with `IsHeckeChar f η` is allowed, so imprimitive characters are included. This
   matches "character of the ray class group modulo 𝔣, extended by zero".

10. **Field model.** `CyclotomicField 3 ℚ` as `Q(√-3)`. Its ring of integers is `𝓞` = `O_K`.

## Differences between the two manuscripts' headline claims (quoted)

- **Region.** Sep 30 abstract: "zero-free in the half-plane `\Re s>7/8`, with the principal
  pole at `s=1` allowed." Oct 5 abstract: "has no zeros in the half-plane `\Rea s>11/12`."
  Since `11/12 > 7/8`, the Oct 5 half-plane is smaller. Oct 5 claims a weaker zero-free
  region than Sep 30, although it appears later. Taken literally, Sep 30 implies Oct 5's claim.
- **Dirichlet characters.** Sep 30 theorem: "The same holds for every Dirichlet
  $L$-function, including $\zeta(s)$." Sep 30 intro: "For a Dirichlet character $\chi$ modulo
  $q$, extended by zero on nonunits" (all characters). Oct 5 intro: "For a primitive Dirichlet
  character $\chi$ of conductor $q$". Oct 5 abstract: "every Dirichlet $L$-function, including
  Riemann's zeta function". Oct 5 says "every Dirichlet L-function" in its headline but
  "primitive" in its body (Oct 5 intro: "for every primitive character $\chi$, independently of
  both conductor and height").
- **Riemann hypothesis / quasi-RH.** Sep 30: "resolves the quasi-Riemann hypothesis
  affirmatively: the supremum of the real parts of the nontrivial zeros of $\zeta$ ... is at most
  $7/8$." Oct 5: "We establish the quasi-Riemann hypothesis by proving..." with `\Rea s>11/12`.
  Sep 30 says the boundary `Re s = 7/8` is not included. Oct 5 asserts "In particular, this rules out
  the existence of Landau--Siegel zeros." Sep 30 says "any exceptional real zero in (7/8,1) is
  excluded." Both are consistent with their regions.
- **Quasi-RH definition.** Sep 30: "a fixed `\sigma_0<1`" (the uniform gap). Oct 5: "a single
  `\varepsilon>0` valid for every primitive character."
- **Hecke.** Both: every finite-order Hecke `L`-function over `\mathbb Q(\sqrt{-3})` has no
  zero in the stated half-plane. Oct 5 body: "finite-order Hecke L-function over K" (no
  primitive/imprimitive restriction stated). Sep 30 defines it with modulus `\mathfrak f` and
  extension by zero, which covers all moduli.
-/
