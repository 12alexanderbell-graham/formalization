# Interpretive choices (blind)
- Solution class: abstract pair (w, φ) of functions ℝ → ℝ in a structure `IsSolution`: w 0 = 0; for every s ≥ 0, HasDerivWithinAt w (φ s) (Ici 0) s; ContinuousWithinAt φ (Ici 0) 0; for s > 0, HasDerivAt φ (-(2/s) φ s - exp (w s)) s. The theorem is universally quantified over such (w, φ); uniqueness is not assumed or stated separately. w'(0)=0 is not an extra hypothesis (it follows from the ODE and continuity, as in the brief).
- mass s = s^2 * (-φ s) * exp (w s / 2) / sqrt (4π).
- N μ = Set.encard {s | 0 ≤ s ∧ mass s = μ} : ℕ∞. Finite counts are Nat casts into ℕ∞ (e.g. ((2k+2 : ℕ) : ℕ∞)).
- "Infinite" in (h) is stated as N = ⊤ (equivalent to the set being infinite).
- Sequence ξ : ℕ → ℝ with StrictMono and Tendsto atTop atTop; m_k = mass (ξ k); numeric bounds as real decimal literals, closed inequalities; m_k → sqrt(2/π) via Tendsto.
- (a) is for all real μ > m₀; (e) requires 0 < μ < m₁; (c) and (g) quantify over k : ℕ and real μ strictly between the stated masses.
- The existence of ξ is existential inside the theorem, as in the claim; the statement does not say ξ is unique (it is determined by the data anyway).
- Not compiled.
