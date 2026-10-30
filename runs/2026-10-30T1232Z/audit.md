# Fidelity audit (annex XL): C9 → F8, Bamba et al. 2012 Eqs. (10.38)–(10.51)

Headlines (namespace `Checked.Cosmography.BambaZ`): `lumDist_z_fifth_order`, `angDist_z_fifth_order` (H₀d_L, H₀d_A to z⁵ for every real K and every scale factor C⁵ at t₀ with a(t₀), H₀ ≠ 0; printed D¹–D³, corrected D⁴), `printedDL4z_fails_past`, `printedDA4z_fails_past` (every K ≠ 0), `bambaDLzClaim[Past]_false`, `bambaDAzClaim[Past]_false`, `milne_printedDL4z_fails_past`, `printed_flat_eq`. Definitions: `curvK`, `DL1z`–`DL3z`, `printedDL4z`, `correctDL4z`, `DA1z`–`DA3z`, `printedDA4z`, `correctDA4z`, `seriesZ`, `remLz`, `remAz`, four claims; reuses audited `lumDist` (C6), `angDist` (C7), `redshift`.

- **Frozen:** commit 8c553aa before proof work. Proof commit 974b7a3; statements byte-identical (diff removes only `sorry`). Promotion adds referee notes to the docstring only.
- **Source:** typeset v3 p. 110 read as images (`typeset/`); v1 p. 107, v2 p. 108 identical (pdftotext of the block). Upstream CS 2009 Eqs. (31)–(52) identical (referee crop).
- **Blind restatement:** `blind/C9_blind.lean` (own definitions; C⁶ near t₀, a₀ > 0, H₀ > 0, c > 0; K ∈ {−1,0,1}; remainder O(z⁶) on 𝓝[≤] t₀ — stronger than our o(z⁵), so our refutation is the stronger statement). Closed in Lean (`Work/Cosmography/BambaZAudit.lean`, `C9Audit`): `printed_eq` (same transcription of all eight printed coefficients), `derived_eq` (blind's derived D⁴ = our corrected D⁴), `SK_eq`, `q0_eq`, `curv_eq`, `dL_eq`, `dA_eq`, `remL_eq`, `remA_eq` (definitions and residuals agree at c = 1), `blindDL_false_via_ours`, `blindDA_false_via_ours`. Same model family for restater, referee and prover (annex 40.2).
- **Not vacuous:** a = eᵗ, K = 1, t₀ = 0 satisfies every hypothesis (used in the refutations and in the blind closure).
- **Not trivial:** the general theorem needs the fifth-order curved y-series (F6/F7) plus an exact identity (1+z)⁵[S_y(z/(1+z)) − S_z(z)] = z⁶W(z) (sympy-generated, checked by `field_simp; ring`) and a y→z transfer lemma (y⁵ = z⁵(1+z)⁻⁵).
- **Bites on examples:** Milne exact H₀d_L = z + z²/2: corrected series exact, printed off by −z⁵/120 (blind, referee); referee exact models a = cosh t, sinh t, eᵗ (K = ±1), Mattig dust: difference k²/120 each.
- **Near-misses:** printed D⁴ fails iff K ≠ 0 (with a₀, H₀ ≠ 0); D¹–D³ printed are certified correct by the headline; flat case printed = correct.
- **Junk values:** local theorem; `curvK` divides by H₀²a₀² ≠ 0; (1+z) ≠ 0 proved from a(t) ≠ 0 near t₀ before dividing; claims assume a > 0 everywhere, H₀ > 0.
- **Types/quantifiers:** ∀ K ∈ ℝ (K = ±1 instances); o(z⁵) (weaker than printed O(z⁶)); two-sided and past-only both refuted.
- **Readings:** "10j²" = 10j₀², "+ (newline) − 27j₀" = −27j₀ (flat parts confirm). "Valid only to O(χ⁵)" reading considered and rejected (D⁴ would be content-free; (10.31) and CS (32) claim O(D⁶)).
- **Classification:** Source error, inherited (CS 2009); truncation from Visser 2004 Eq. (40), legitimate there.
- **Referee** (`referee/referee_c9.py`, `.out`): STANDS-WITH-CORRECTIONS; corrections adopted (provenance, origin, size, proof dependence on F6 machinery). Side result: C10 second route.
- **Axioms:** `#print axioms` on the headlines: `propext, Classical.choice, Quot.sound` (local; CI in STATE).
