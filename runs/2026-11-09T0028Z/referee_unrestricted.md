# Referee report: unrestricted Falkner–Skan class (run 2026-11-09T0028Z)

Referee: an Opus subagent with no stake in the result. Files read in full: Work/FalknerSkan/Unrestricted.lean (frozen at d71bf54), runs/2026-11-09T0028Z/coppel/REPORT.md, and the statements of the matching theorems in Checked/FalknerSkan/{Bounded,HalfBounded,FifthBounded}.lean. I listed the lemmas and read the main-theorem header of runs/…/lean/Unrestricted.lean (0 `sorry`). I did NOT recompile it. My scripts are in /tmp/claude-0/referee_unres/ (outside the repo). I edited no repository file except this one.

## Verdict: STANDS-WITH-CORRECTIONS (prose only; the statements need no change)

## 1. Statement attack
- **Equations.** Each `hq` agrees with the docstring's ODE solved for f''':
  - β-form: q' = −f q − β(1 − p²).
  - Hiemenz: q' = −f q − 1 + p².
  - Homann: q' = −2 f q − 1 + p².
  - β = 1/2 and β = 1/5: q' = −f q − (1/2)(1 − p²) and q' = −f q − (1/5)(1 − p²). Lean parses `1 / 2 * (1 - p η ^ 2)` as (1/2)(1 − p²), as intended.
  - Setting β := 1/2 or 1/5 in `fs_monotone_of_limit` gives the `hq` of the corresponding window theorem syntactically. For Hiemenz the two forms differ and need a `ring` congruence.
- **Boundary conditions and derivatives.** The derivative at 0 is one-sided (`HasDerivWithinAt … (Ici 0)`). At η > 0 it is two-sided, because Ici 0 is a neighbourhood of η. f(0) = p(0) = 0 and `Tendsto p atTop (𝓝 1)` are the standard FS conditions. Values at η < 0 are junk and the statements never use them. The derivative hypotheses give continuity of f, p, q on [0, ∞).
- **"No bound on f'" is exactly what changed.** Each window or equality theorem is the matching Checked `*_bounded_*` theorem character for character (Bounded.lean:13–52, HalfBounded.lean:33–71, FifthBounded.lean:37–75), with `hb`/`hb₂ : ∀ η ∈ Ici 0, -1 ≤ p η ∧ p η ≤ 1` deleted and nothing else changed. The windows are identical: 1.2325876568–9, 1.3119376938–9, 0.927680039–40, 0.6867081809–11.
- **Non-vacuity.** Checked `*_exists_bounded` gives a solution that satisfies every hypothesis, so no theorem is vacuous.
- **Hypotheses.** None is superfluous: f(0) = 0 is essential, since it is what forces f(η₂) < 0 in L6 when η_z = 0. None is missing.
- **Quantifiers.** The equality theorems claim equality only on Ici 0, which is correct. The β range is 0 < β ≤ 1 and excludes Blasius (β = 0). That is acceptable: the K-form proof needs K = 1/β finite, and the docstring claims only 0 < β ≤ 1.
- **Remark.** Homann (K = 2) is β = 1/2 after scaling (HalfBounded already derives one from the other). So `homann_*` and `fs_half_*` are one mathematical result stated twice. This is not a defect.

## 2. Independent derivation (all checks passed)
- **Scaling.** For F(s) = c f(s/c) with c = √β, β·(F''' + (1/β) F F'' + 1 − F'²) = f''' + f f'' + β(1 − f'²) at η = s/c. This is exact in sympy (ids.py). So K = 1/β ≥ 1 exactly when 0 < β ≤ 1, and the scaling preserves the sign of the second derivative, the limit of the first derivative, and the conditions at 0.
- **Identities.** With r = −K f q − 1 + p²:
  - r' = −K f r − (K−2) p q
  - (Λr)' = (2−K) Λ p q
  - Φ' = −Λ q (q + 2(K−1) f p) for Φ = Λ(f r − p q)
  - Ω' = 2(K−2) M f² q for Ω = M(p² − 1 − 2 f q)

  I re-derived all four by hand and checked them in sympy, with Λ = exp(K∫f) and M = exp(2∫f) (ids.py: all residuals 0).
- **L3 / L3′.** The line (f(η₁) + s(η−η₁), s, 0) solves the system exactly when s² = 1. Backward uniqueness then gives p(0) = s ≠ 0. An interior maximum of p equal to 1 has q = 0, so L3′ follows. Correct; this is the remaining Lean obligation (`htouch`).
- **L4.** a := sSup{η ∈ [η′, η″] : q ≤ 0} gives q(a) = 0 and q'(a) ≥ 0 from the right quotient. But q'(a) = p(a)² − 1 < 0, because −1 < p(a) on [T, ∞) and p(a) < 1 by L3′. Then p is antitone and lim p ≤ p(η′) < 1. Correct.
- **L5.** Correct. The T in η₂ := sSup{η ∈ [0, T] : q ≤ 0} must be L4's T (q > 0 on [T, ∞)); REPORT.md leaves this implicit.
  - If η₂ = 0, then q(0) = 0 by right continuity, and r(0) = −1 < 0 contradicts q > 0 on (0, ε).
  - q'(η₂) ≥ 0 gives p(η₂)² ≥ 1. Then p ≤ 1, L3′ (p ≠ 1) and L3 (p ≠ −1) give **p(η₂) < −1**.
  - q'(η₂) > 0 together with the two-sided derivative gives the left neighbourhood where q < 0.
- **The η_z construction.**
  - If η₂ − δ/2 < 0, Sz is empty and (0, η₂) ⊂ (η₂ − δ, η₂), so the empty case still works.
  - Sz empty: η_z = 0 with r(0) = −1 ≤ 0 and p(0)q(0) = 0.
  - Sz non-empty: q(η_z) = 0 by continuity, and r(η_z) ≤ 0 from the right quotient.
- **L6 (Descent).** Correct.
  - In the case "Sz empty", η_z = η_d = 0 and p < 0 on (0, η₂], so f(η₂) < f(0) = 0 at once. The written route (Φ(0) = Λ f(0) r(0) = 0 > Φ(η₂) ≥ 0, or r(0) = −1 against r(η_d) > 0) also closes it.
  - On (η_d, η₂): f > 0, p < 0, q < 0 and K ≥ 1 give q + 2(K−1) f p < 0. With −Λq > 0 this gives Φ' < 0.
  - Φ(η₂) = Λ f(η₂)(p(η₂)² − 1) because q(η₂) = 0 and r(η₂) = p(η₂)² − 1.
  - In the branch η_d > η_z: p(η_z) > 0 forces q(η_z) = 0. Then p ≥ 0 and q ≤ 0 on [η_z, η_d], and K ≤ 2 gives (Λr)' ≤ 0.
- **L7 (Ascent).** Correct. Φ' < 0 on (η₂, η₀) needs only K ≥ 1. (Λr)' ≥ 0 on [η₀, ∞) needs K ≤ 2. The final contradiction needs only that p is bounded above, not p ≤ 1 specifically; p → 1 would do. There is no gap.
- **L8 (Omega, K ≥ 2).** Correct. It needs neither f(η₂) nor K ≥ 1: Ω(η₂) = M(p² − 1) ≥ 0 and Ω' ≥ 0. Beyond max(η₂, T), p² ≤ 1, f > 0 and q > 0 give Ω < 0.
- **Where K enters.** K ≥ 1 is used only in the sign of Φ' (L6, L7), as REPORT.md claims. K ≤ 2 enters through (Λr)', and K ≥ 2 through L8.
- **Numerical check (my own).** I ran DOP853 at rtol 1e-11 for K ∈ {1, 1.5, 2, 5} and s ∈ [−4, 3] (281 values).
  - Every bottom of q has f < 0. One apparent exception at K = 1, s = 1.2 was a grid-sampling artefact: an event-located zero gives f(η₂) = −0.1135 at η₂ = 11.859 with p = −1.046.
  - For K = 0.5, a shooting root for p → 1 exists near s ≈ 1.13–1.15, consistent with REPORT's non-monotone K < 1 example. These are floating-point checks, not part of the proof.

## 3. Prior art
- **Read verbatim** (pdftotext, arxiv.org/pdf/2011.07725, Fazio): "Coppel [8] and Craven and Peletier [9] pointed out that the above restriction on the first derivative can be omitted when 0 ≤ β ≤ 1." The restriction meant is 0 < f′ < 1, and the quoted range includes β = 1.
- **Read verbatim** (Cambridge PDF, Tam, Canad. Math. Bull. 13 (1970) 125–127): "In 1960, Coppel [1] proved the existence (and uniqueness with the assumption 0 < f' < 1)". Tam proves existence only, by shooting.
- **Not accessible**: Craven & Peletier, Mathematika 19 (1972) 129–133. The PDF is paywalled (I got HTML), and the scilit and Cambridge pages give no abstract or result. I also could not get Coppel 1960, Hartman ch. XIV or Veldman–van de Vooren 1980.
- **Conclusion on the theorem.** By the secondary source quoted above, it is in print: every solution for 0 ≤ β ≤ 1 lies in the class 0 < f' < 1, with β = 1 included, attributed to Coppel 1960 and Craven–Peletier 1972. I have not verified which of the two proves which part, or whether β = 1 is closed or open in the originals. **The theorem should be presented as a formalization of a classical result, not as new.**
- **Conclusion on the argument.** I found no source for the specific weighted quantities Φ = Λ(f q' − p q) and Ω = M(p² − 1 − 2 f q), or for the descent/ascent scheme. Whether this is Coppel's or Craven–Peletier's argument is UNKNOWN; their texts were not read.

## 4. Required corrections (prose; no statement change)
1. **REPORT.md "Prior art"** should say "in print per a secondary source (Fazio, read verbatim), primary texts unread", not "unconfirmed". Remove any implied novelty of the result; state that only the argument's provenance is unknown. The same applies to the run README and to any promotion docstring.
2. **REPORT.md L5** should name T as L4's T (q > 0 on [T, ∞)), and note that if η₁ ≥ T then q(η₁) > 0, so the set is nonempty.
3. **REPORT.md Theorem** should note that Sz is also empty when η₂ − δ/2 < 0, and that (0, η₂) ⊂ (η₂ − δ, η₂) in that case.
4. **REPORT.md Remark (K = 2)**: "q is strictly decreasing" does not by itself give q > 0. Add: if q(η) ≤ 0, then q ≤ q(η) + (negative) afterwards, so p → −∞, contradicting p → 1.
5. **The docstring of the eventual Checked module** should say that Homann ≡ β = 1/2 by scaling, so readers do not count them as separate results. This is optional.
6. **Lean.** The remaining obligations are L3 (`htouch`, via backward uniqueness) and the β-form ↔ K-form scaling transfer for `fs_monotone_of_limit`, including Hiemenz's `ring` congruence. The plan as checked above has no mathematical gap.
