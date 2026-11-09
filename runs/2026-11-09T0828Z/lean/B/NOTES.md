# Fork B notes (run 2026-11-09T0828Z): Lemmas I, L, R of the β < 0 research note

Scratch Lean, compiled with `lake env lean runs/2026-11-09T0828Z/lean/B/<File>.lean` against the built
`Checked.FalknerSkan.LimitCore` (reuses `mono`, `smono`, `cont_of`, `at_of`, `left_neg`).
System (scaled, pressure sign +): f' = p, p' = q, q' = −K f q + 1 − p², all as
`HasDerivWithinAt … (Ici 0)` on `Ici 0`.

| file | main theorem(s) | status | compile |
|---|---|---|---|
| `SlowInv.lean` | `Scratch0828.SlowInv.slow_inv` | green, 0 sorry | ≈ 6 s |
| `NegLimit.lean` | `Scratch0828.NegLimit.neg_limit`, `exceeds`, `f_tendsto` | green, 0 sorry | ≈ 13 s |
| `Riccati.lean` | `Scratch0828.Riccati.riccati_up` | green, 0 sorry | ≈ 9 s |

`#print axioms` for every main theorem: `[propext, Classical.choice, Quot.sound]`.

## Statements (hypotheses hf, hp, hq as above)

- `slow_inv` (Lemma I): `0 < K`, `0 < μ`, `μ + 2 / μ ≤ K * θ`, `0 ≤ η₀`, and at η₀:
  `0 ≤ p η₀`, `p η₀ < 1`, `0 < q η₀`, `q η₀ < μ * (1 - p η₀)`, `θ < f η₀` ⊢
  `∀ η ∈ Ici η₀, 0 ≤ p η ∧ p η < 1 ∧ 0 < q η ∧ q η < μ * (1 - p η) ∧ θ < f η`.
- `neg_limit` (Lemma L): `0 < K`, `0 ≤ a`, `∀ η ∈ Ici a, 0 < q η`, `-1 < p a`, `∀ η ∈ Ici a, p η < 1`
  ⊢ `Tendsto p atTop (𝓝 1)`. (`exceeds`: same hypotheses, `L < 1` ⊢ `∃ η ∈ Ici a, L < p η`.)
- `f_tendsto`: hf, `Tendsto p atTop (𝓝 1)` ⊢ `Tendsto f atTop atTop`.
- `riccati_up` (Lemma R): `0 < K`, `0 < μ`, hp, hq, `0 ≤ a`, `∀ η ∈ Ici a, p η < 1`,
  `Tendsto f atTop atTop`, `∀ η ∈ Ici a, μ * (1 - p η) ≤ q η` ⊢
  `∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - p η) ≤ q η`.

## Comparison with the note's mathematics (no gap found; three simplifications)

1. **Lemma I:** W' = (μ − Kf)W + g(μ² − μKf + 2 − g) (g = 1 − p, W = q − μg) re-derived and used only
   at a zero of W, where W' = g(μ² − μKf + 2 − g) < 0. So the integrating factor exp∫(Kf − μ) is not
   needed: a first-touch argument on the closed "bad" set (sInf of a closed set) suffices. g(τ) > 0
   comes from (1 − p)e^{μη} nondecreasing (its derivative is e^{μη}(μ(1 − p) − q) > 0), as in the note.
   q(τ) > 0 by Lemma 1 (q' = 1 − p² > 0 at a zero). K > 0 is used (μKf > μ² + 2 from f > θ).
2. **Lemma L:** the note's route works as written (φ = q − c/(2K(B + η)), B = |f(a)| + 1 so B + η ≥ 1;
   f ≤ B + η from p < 1; φ cannot stay ≤ 0; once positive it stays positive by first touch; then
   p − (c/2K) log(B + η) is nondecreasing). Proved in the form "p exceeds every level L < 1", which
   gives the limit by monotonicity without a supremum; c = min(1 − p(a)², 1 − L²).
3. **Lemma R:** the hypotheses p → 1 and q > 0 of the note are not needed (only f → ∞, p < 1 and
   q ≥ μ(1 − p)); hf is not needed either. Step "r cannot climb back to M" is done on W_M = q − M(1 − p)
   by first touch (at a zero W_M' = g(M² − MKf + 2 − g) < 0 since MKf ≥ M² + 3M/μ ≥ M² + 3); the
   descent step uses r = q/(1 − p), r' = r² − Kfr + 2 − g ≤ −1 while μ ≤ r < M, as in the note
   (M replaced by max M μ).
