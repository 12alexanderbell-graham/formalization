# Adversary report: hypothesis necessity check

Test files (all compiled against NonVacuity_new.lean):
/tmp/claude-0/-home-claude-formalization/a83b129e-558b-5d0f-8d12-789f24f41634/scratchpad/adv/T1.lean, T2.lean, T3.lean

## F1 (HIGH): junk values make REDUNDANT mean "redundant in Lean", not "redundant in the science"
Compiled:
```lean
theorem junk1 (x : ℝ) (hx : x ≠ 0) : 1 / (1 / x) = x := by simp
example : dropped% junk1 1 := fun x => by simp
```
The report prints "hypothesis 1 redundant (headline weaker than what is proved)". A scientist reads
`x ≠ 0` (nonzero denominator, mass, etc.) as a real assumption. Lean's `x/0 = 0` convention makes the
statement true without it. Any `/`, `⁻¹`, `Real.sqrt`, `Real.log`, `ℕ`-subtraction, or `Finset.sum`
over an empty range has the same effect. The same mechanism makes NEEDED too weak in the other
direction: a hypothesis can be labelled needed only because the conclusion fails at a junk value.
Fix: print the tag as "redundant in Lean (may be a totalisation artefact)". Better, give a second
tag for hypotheses whose statement mentions `/`, `⁻¹`, `sqrt`, `log`, `-` on `ℕ`, so a human reviews them.

## F2 (HIGH): redundancy is per-hypothesis, and duplicated or mutually implying hypotheses are all reported redundant
Compiled:
```lean
theorem dup (x : ℝ) (h1 : 1 < x) (h2 : 1 < x) : 0 < x := by linarith
example : dropped% dup 1 := fun x h2 => by linarith
example : dropped% dup 2 := fun x h1 => by linarith
```
The report says "redundant 1, 2", which reads as "both can be deleted". Deleting both makes the
statement false (`¬ ∀ x : ℝ, 0 < x`, compiled). It is the same for `(h1 : 1 < x) (h2 : 2 < x)`.
Neither hypothesis is ever NEEDED, so a headline with a genuinely load-bearing but doubly stated
assumption shows only "redundant". Fix: when two or more hypotheses of one headline are labelled
REDUNDANT, add "individually redundant; not jointly". Optionally also check `dropped%` for the set.

## F3 (MEDIUM): the check numbers and classifies hypotheses that CLAIMS.md does not list
`numHyps` and `flatStatement` unfold `Checked` definitions at the head and also at the conclusion, so
binders inside the unfolded definition become "hypotheses". CLAIMS.md does not unfold. Compiled:
```lean
def Conv (a : ℕ → ℝ) (L : ℝ) : Prop := ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, |a n - L| < ε
theorem conv (a : ℕ → ℝ) (h : ∀ n, a n = 1) : Conv a 1 := ...
#eval nh ``conv                      -- 2   (CLAIMS.md lists 1 assuming line)
example : necessity% conv 2 := ⟨fun _ => 1, fun _ => rfl, 0, by simp; exact fun x => ⟨x, le_refl _⟩⟩
```
Elaborated obligation: `∃ a ε, ∃ (_ : 0 < ε), ...` (hyp 1), and for hyp 2: `∃ a, ∃ (_ : ∀ n, a n = 1), ∃ ε, ¬∃ N, ...`.
The report says "conv: needed 1, 2", but hypothesis 2 is the `ε > 0` guard of a definition. It inflates the
needed tally and points at a number the reader cannot find in CLAIMS.md.
Also compiled:
- `theorem viaDef (x : ℝ) : Claim x` with `def Claim x := 0 < x → x ≤ 1 → x^2 ≤ 1` has 2 hypotheses in the
  check and 0 in CLAIMS.md. Every extra hypothesis sits after the real ones, so the real numbers stay aligned.
  Only the count `(k)` and the tail differ.
- `theorem withLet : let a : ℝ := 2; 0 < a → a ≠ 0` has 1 hypothesis in the check (`whnfR` zeta-reduces the let)
  and 0 in CLAIMS.md. This needs a contrived statement (LOW).
Fix: either have the CLAIMS generator use the same flattening, or make the check number only the binders
that precede the first unfolded definition, and report the rest as "inside definition X".

## F4 (MEDIUM): trailing `P → False` makes the last hypothesis disappear (count and numbering mismatch)
Compiled:
```lean
theorem two (x : ℝ) (h1 : 0 < x) (h2 : x < 0) : False := by linarith
#eval nh ``two          -- 1   (CLAIMS.md: 2 assuming lines)
#check (necessity% two 1)   -- ∃ x, x < 0
theorem two' (x) (h1 : 0 < x) (h2 : 1 < x) (h3 : x < 1) : False  -- check: 2, CLAIMS: 3
```
For a `False`-conclusion theorem (an inconsistency or no-go theorem) the last assumption is never classified.
The report says "(k)" with k one smaller than the number of assuming lines. If the first k classifications are all
"needed", the headline counts as fully classified, although the last assumption was never examined.
Fix: either treat the last binder as hypothesis k+1 with `necessity%` = "∃ other binders, P" (and the symmetric dropped),
or report "last assumption read as conclusion" for these headlines. At minimum make the CLAIMS generator apply the same rule.

## F5 (LOW): "no obligation" can be forced by the author, hiding a decorative hypothesis
Compiled:
```lean
theorem launder (x : ℝ) (h : x = x) : x ^ 2 ≥ 0 ∧ h = h := ⟨sq_nonneg _, rfl⟩
#check (necessity% launder 1)   -- error: hypothesis 1 is used as data by the conclusion: no obligation
```
Adding a conjunct `h = h` (or a dependent `if`/subtype) moves a hypothesis from "open" to "no obligation".
The report text "proof used as data" is honest, but a tally that excludes DATA hypotheses from "fully classified"
would not catch this. Since `nHeadAll` requires `dataH.size == 0`, it is not hidden from that count. This is acceptable
if the DATA list is reviewed. Consider a warning when the data use is only `Eq.refl`-like, or when the proof is used only in the conclusion.

## F6 (LOW): the hash lookup ignores binder names and binder info
`Expr.beq` returned `true` for `∀ {x : ℕ}, x = x` versus `∀ (y : ℕ), y = y` (compiled, with equal hashes). So a Checked
theorem with different implicitness or names still counts as the witness. The meaning is the same, so there is no
mislabel. It only means the witness is "up to binder annotations". Nothing else was found in the hash path. The witness
is any Checked theorem type, so soundness of the label rests on the axiom and sorry audit of the witness (not examined here).

## Tried and did NOT break it
- `s ⊆ t` (Set and Finset) conclusions, `f ≤ g` on functions, `x ≠ y`, `a ∉ s`, `StrictMono`/`Injective` conclusions: no
  phantom hypotheses (`whnfR` does not expose a `∀`). Counts matched CLAIMS.
- `¬¬P` simplification: `nn (x) (h : 0 < x) : ¬¬(0 < x*x)` gives `∃ x, ¬0 < x*x`, which is correct.
- `∃`/`↔` conclusions and implicit or `autoParam` binders (`imp {x} (h : 0 < x := by norm_num)`): counted once, same as CLAIMS.
- Universe-polymorphic statements: the obligation keeps the level parameter `u`. A witness with another universe
  name just stays OPEN, which is safe.
- Hypothesis used by a later binder, or by the conclusion: reported as "no obligation", as documented.
- Junk-value NEEDED (hypothesis needed only because of a Lean convention): I could not build a convincing case that
  a scientist would call the hypothesis unneeded. The general caveat is in F1.
