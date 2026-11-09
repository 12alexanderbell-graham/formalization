# Removing the hypothesis −1 ≤ f′: a proof for every K ≥ 1 (run 2026-11-09T0028Z/coppel)

Written by a research subagent (Opus, brief in the run README); the subagent could not write files, so the main session saved its text verbatim below. Every identity and step was re-derived by hand by the main session before formalization (run README); the Lean proof is the check.

## Verdict
PROVED for every real K ≥ 1, so it covers K = 1 (Hiemenz, β = 1), 2 (Homann), 5 and 10. Take f, p, q on [0, ∞) with f′ = p, p′ = q, q′ = −K f q − 1 + p², f(0) = p(0) = 0 and p → 1. Then q > 0 on [0, ∞), so 0 ≤ p < 1 and in particular p ≥ −1. Every such solution therefore lies in the class already handled in Lean.

The proof uses three exact derivative identities (checked symbolically), sign and monotonicity arguments, the IVT, and sups of closed sets. No asymptotics (no q → 0, no decay rates, no Crocco variables).
- K ∈ [1, 2]: the Descent and Ascent lemmas (L6, L7).
- K ≥ 2: a one-line monotone quantity (L8).
- K = 2: q′ = −exp(−2∫₀f) < 0 directly.

K ≥ 1 is used in exactly one place: the sign of Φ′ in L6 and L7. Numerically the Ascent lemma is FALSE for K = 0.9 and K = 0.5, and for K = 0.5 a non-monotone solution exists (min p = −1.40).

The subagent did not read Coppel or Craven–Peletier; it cannot say whether this is their argument.

## Prior art (what could and could not be read)
- NOT ACCESSIBLE: Coppel, Phil. Trans. A 253 (1960) 101–136 (HTTP 403; scilit abstract only: simpler proof of Weyl's existence result, "the properties of all solutions", no range for λ). Craven & Peletier, Mathematika 19 (1972) 129–133 (no preview). Hartman, ODE ch. XIV. Hastings–McLeod, Classical Methods in ODEs (table of contents only: ch. 9 is periodic/oscillatory FS solutions).
- READ verbatim (pdftotext of arXiv:2011.07725, Fazio, arxiv.org/pdf): "Coppel [8] and Craven and Peletier [9] pointed out that the above restriction on the first derivative can be omitted when 0 <= beta <= 1." (the restriction is 0 < f′ < 1).
- READ, WebFetch summaries only (not verbatim): MDPI Fluids 6 (2021) 153: "Craven et al. [9] proved the existence and uniqueness of solutions for 0 ≤ β < 1"; "Tam [8] removed Coppel's assumption of 0 < f′ < 1". Tam, Canad. Math. Bull.: Coppel proved existence "(and uniqueness with the assumption 0 < f′ < 1)"; Tam proves existence without it, with −1 < f′ < 1 along the way.
- β = 1: secondary sources disagree (Fazio ≤ 1; MDPI review and the Veldman–van de Vooren OCR < 1). The proof below covers K = 1 in any case.

## Proof
Hypotheses: all derivatives `HasDerivWithinAt _ _ (Ici 0) η` for η ≥ 0 (two-sided for η > 0): f′ = p, p′ = q, q′ = −K f q − 1 + p², f 0 = 0, p 0 = 0, p → 1. Notation r := −K f q − 1 + p² (= q′). Lemma (a), p ≤ 1 on [0, ∞), is in Lean (scratch of run 2228Z).

**L0 (weights).** Λ(η) := exp(K ∫₀^η f), M(η) := exp(2 ∫₀^η f); both > 0, Λ′ = K f Λ, M′ = 2 f M.

**L1 (identities).** r′ = −K f r − (K−2) p q, and (i) (Λ r)′ = (2 − K) Λ p q; (ii) Φ := Λ (f r − p q) has Φ′ = −Λ q (q + 2(K−1) f p); (iii) Ω := M (p² − 1 − 2 f q) has Ω′ = 2(K−2) M f² q. (Also E := q²/2 − p³/3 + p, E′ = −K f q², not needed.) Pure ring arithmetic after the product rule (`identities.py`).

**L2.** ∃ T, ∀ η ≥ T: 1/2 ≤ p η ≤ 1 and f η > 0 (limit, lemma (a), MVT).

**L3 (touch).** q η₁ = 0 and p η₁ = ±1 is impossible: the line (f η₁ + s(η − η₁), s, 0) solves the system and agrees at η₁; backward uniqueness on [0, η₁] gives p 0 = s ≠ 0. **L3′.** p < 1 on [0, ∞) (an interior maximum p = 1 has q = 0, then L3).

**L4.** ∃ T, ∀ η ≥ T, q η > 0. Take T with p > −1 on [T, ∞). If q η′ ≤ 0 for some η′ ≥ T, then q ≤ 0 on [η′, ∞): otherwise with a := sSup{η ∈ [η′, η″] | q η ≤ 0}, q a = 0, q > 0 on (a, η″], so q′(a) ≥ 0, but q′(a) = p(a)² − 1 < 0. So p is antitone on [η′, ∞) and lim p ≤ p η′ < 1, contradicting p → 1.

**L5 (last zero).** If q η₁ ≤ 0 for some η₁ ≥ 0, there is η₂ > 0 with q η₂ = 0, q > 0 on (η₂, ∞), p η₂ < −1, and q < 0 on (η₂ − δ, η₂) for some δ > 0. (η₂ := sSup{η ∈ [0, T] | q η ≤ 0}; η₂ ≠ 0 because q′(0) = −1; q′(η₂) ≥ 0 gives p(η₂)² ≥ 1; L3 and p ≤ 1 give p η₂ < −1; then q′(η₂) > 0.)

**L6 (Descent; 1 ≤ K ≤ 2).** If 0 ≤ η_z < η₂, q < 0 on (η_z, η₂), q η₂ = 0, p η₂ < −1, r η_z ≤ 0 and p η_z · q η_z = 0, then f η₂ < 0. Proof: suppose f η₂ ≥ 0. p strictly decreases on [η_z, η₂]. Let η_d := η_z if p η_z ≤ 0, else the zero of p in (η_z, η₂) (IVT); p η_d q η_d = 0 and p < 0 on (η_d, η₂]. f strictly decreases on [η_d, η₂], so f > 0 on [η_d, η₂). On (η_d, η₂), f p q > 0, so with K ≥ 1, Φ′ < 0 and Φ η_d > Φ η₂ = Λ f(η₂)(p(η₂)² − 1) ≥ 0. Φ η_d = Λ f(η_d) r(η_d), so r η_d > 0. If η_d = η_z, contradiction. Otherwise on [η_z, η_d], p ≥ 0, q ≤ 0, so (Λr)′ ≤ 0 (K ≤ 2) and Λ r η_z ≥ Λ r η_d > 0, contradiction.

**L7 (Ascent; 1 ≤ K ≤ 2).** If q η₂ = 0, p η₂ ≤ −1, f η₂ ≤ 0, q > 0 on (η₂, ∞), p ≤ 1 and p → 1, then False. p strictly increases on [η₂, ∞); IVT gives η₀ > η₂ with p η₀ = 0, p < 0 on [η₂, η₀), so f < 0 on (η₂, η₀]. There f p q > 0, so Φ′ < 0 (K ≥ 1) and Φ η₀ < Φ η₂ = Λ f(η₂)(p(η₂)² − 1) ≤ 0; Φ η₀ = Λ f(η₀) r(η₀) with f η₀ < 0, so r η₀ > 0. On [η₀, ∞), p ≥ 0 and q > 0, so (Λr)′ ≥ 0 (K ≤ 2), r > 0, q ≥ q η₀ > 0, and p η ≥ q η₀ (η − η₀) is eventually > 1. Contradiction.

**L8 (Omega; K ≥ 2).** If q η₂ = 0, p(η₂)² ≥ 1 and q > 0 on (η₂, ∞), then False: Ω η₂ ≥ 0 and Ω′ ≥ 0 on [η₂, ∞), but for η beyond max(η₂, T) (T from L2), p² − 1 ≤ 0, f > 0, q > 0 give Ω < 0.

**Theorem.** For K ≥ 1, q > 0 on [0, ∞); hence 0 ≤ p < 1. Suppose q η₁ ≤ 0; L5 gives η₂. K ≥ 2: L8. 1 ≤ K ≤ 2: Sz := {η ∈ [0, η₂ − δ/2] | q η ≥ 0}; if empty, η_z := 0 (r 0 = −1, p 0 q 0 = 0); else η_z := sSup Sz (q η_z = 0, r η_z ≤ 0 from right quotients). L6 gives f η₂ < 0, L7 gives False.

**Remark (K = 2).** By L1(i), Λ r ≡ −1, so q is strictly decreasing.

## Numerical checks (floating point, scipy DOP853, rtol 1e-10 to 1e-11; `numcheck.py`)
- `identities.py`: all five identities verified exactly in sympy.
- Trajectories from (0, 0, s), s ∈ [−4, 3] (141 values), K ∈ {1, 1.5, 2, 5, 10}: every bottom (zero of q with q′ > 0) has f < 0 and is followed by p crossing 1 (bottoms: 105, 106, 1, 0, 0; violations 0).
- Random states (400 per K, K ∈ {1, 1.5, 2}): from a bottom with f ≤ 0 p always crosses 1 (0/400 violations); from a top every later bottom has f < 0.
- K < 1: K = 0.5, s ≈ 1.1257867: top at η = 1.58 (p = 0.754), bottom at η = 5.70 (p = −1.4015, f = −0.0056), then p → 1 within shooting precision; there Φ rises from −0.10 to +2.87 and r(η₀) = −0.30 (L7 fails). The L7 statement fails for K = 0.9 and 0.5 on random bottoms (1/300, 6/300).

## Gaps and formalization notes
- No known mathematical gap. Lean obligations: L0 (FTC), L1 (ring after product rule), monotonicity from derivative signs, three sSup constructions (L4, L5, η_z), IVT twice. L3 from the existing `start_of_touch`/`uniq_left`; L4 is the existing fencing argument started at T.
- Prior art unconfirmed; the β = 1 status in print conflicting. The numerics are uncertified and not part of the proof.
