# External test, target 0: Chandrasekaran, "An algebraic quantization of gravity from the null cone"

arXiv 2611.34924v1 (2026-11-25), Stanford; built with OpenAI's GPT-6 Astra ("several of the calculations
and proofs ... developed through detailed, back and forth collaboration with GPT-6 Astra", Acknowledgements).
Run 2026-11-26T1529Z. Files under `runs/2026-11-26T1529Z/T0/`. Whether this is the right quantum theory of
gravity is not a question the system answers; it certifies the paper's claims inside its own framework.

**Verdict: NOT DONE.** (a) is certified within the paper's own definitions; (b) is certified from the
heat-kernel input onward; (c) only its algebraic core. Blocking links: `EXTERNAL_BLOCKERS.md` rows 0(b), 0(c), 0.

## (a) Finite graviton pair amplitude, Eqs. (4.33)–(4.34) — certified as stated

Blind reading: brief committed first (4c1eda2), then a fresh Sonnet reader read PDF pages 27 and 33–35 only
and wrote `reading.lean` (commit after it). All five reader theorems proved in Lean (Mathlib, axioms
propext, Classical.choice, Quot.sound; checked with Lean 4.34.1 / Mathlib d13f23b):

- `single_mode`: on the Fock space of one mode (q⁰ = p⁰ = 0, (Δq_k)² = 1/(2sk), q̂ = Δq(𝔞+𝔞†)), the
  connected correlator ⟨(e^{ik𝔞†𝔞/s} q̂² e^{−ik𝔞†𝔞/s}) q̂²⟩_c = 2(Δq_k)⁴ e^{−2ik/s}; zero between
  different modes (`closure_b.lean`).
- `eq_4_33`: absolute convergence for every s > 0, double sum = diagonal sum, and the limit
  Li₂(e^{−2i/s})/(2s²) (`closure_a.lean`).
- `eq_4_34`: the G_N³ Taylor coefficient at finite N is exactly −(i/s³) H_N (three derivative steps of a
  closed family, `closure_c.lean`); `harmonic_log`: H_N − log N = O(1).
- `finite_term`: Im[Li₂(e^{−2i/s})/(2s²)] = −log s/s³ + O(1/s³) as s → ∞, and the ratio to −log s/s³ → 1
  (`closure_d.lean`, via |Σ sin(kθ)/k² − θ log(1/θ)| ≤ 4θ for 0 < θ ≤ 1/2, split at K = ⌊1/θ⌋).

What "finite" depends on (reader's list, checked):
1. fixed corner area, s = 𝒜/(4G_Nħ) > 0 — needed (the bound is per s; the G_N → 0 expansion diverges as log N);
2. one polarization and one real angular harmonic — **the certified statement covers one harmonic only.**
   The text gives no dependence of the variance on the angular momentum; if every harmonic carried the
   same radial tower, the sum over harmonics (2ℓ+1 each) of the same nonzero value would not converge.
   The sentence "the sum over graviton pairs of arbitrarily short wavelength thus defines a finite
   amplitude" is established for short radial wavelength in one harmonic, not for short angular wavelength;
3. Gaussian state with q⁰ = p⁰ = 0 — with nonzero centres the connected correlator gains one-graviton
   exchange terms 4(q_k⁰)²(Δq_k)² e^{−ik/s}, finite only if Σ (q_k⁰)²/k converges (not certified);
4. the chosen annihilation phase — **not needed for finiteness**: without it the sum is π²/(12s²)
   (`closure_e_nophase.lean`); the phase matters only for the expansion in G_N;
5. the order of limits — certified both ways: N → ∞ at fixed s is finite; expanding in G_N first gives the
   −(i/s³)(log N + O(1)) divergence.

What the claims page should say: "For one polarization and one angular harmonic, in the Gaussian state
centred at zero, the paper's pair-creation-and-annihilation sum converges absolutely for every G_N > 0
and equals Li₂(e^{−2i/s})/(2s²); its G_N³ Taylor coefficient diverges like log N; its imaginary part is
−log s/s³ + O(1/s³). Certified in Lean from a blind reading. Not certified: the sum over angular harmonics
and polarizations, and the paper's general finiteness argument (unitarity and Cauchy–Schwarz on its
Hilbert space)."

## (b) One-loop black hole entropy, Section 4.7 — arithmetic certified, input not

`entropy_b.lean`: 53/(45(4π)²)·(8π)²·log s^{1/2} = (106/45) log s; with the measure's 1/2 and s ∝ ℓ²,
q/(1−q) = 257/45 ⟺ q = 257/302; at fixed mass q/(2(1−q)) − 1/2 = 106/45 per log s = 212/45 per ln a
(s ∝ a²), which is Sen's C_local = 424/90 for pure gravity, the coefficient of his mixed ensemble
(mass fixed, angular momentum summed; arXiv 1205.0971 eqs. (1.2), (1.4), read by a fetch subagent).
It is not Sen's singlet-ensemble value (212/45 − 3) ln a, the "77/45" often quoted; the paper's phrase
"Sen's classic result" refers to the J-summed ensemble, as its text says ("with angular momenta summed").

Candidate finding withdrawn: the footnote's q = 2x²/(1+x²) (x = (1−ε)r_h/ℓ(𝒟)) and the one-loop q = 257/302
seemed to conflict for a freely chosen ℓ(𝒟)/r_h. A referee subagent (fresh, sections only) showed r_h is
defined in the clock-truncated state (4π r_h² = ⟨Â⟩), so x is an output: the two together fix
x² = 257/347, i.e. ℓ(𝒟)/r_h = (1−ε)√(347/257) ≈ 1.162(1−ε), inside the paper's window
257/302 ≤ x ≤ √(257/302) (certified). Residual (presentation): the paper never states this implied ratio,
and its sentence "we must specify how the maximum clock reading scales with horizon area" reads as a free
choice.

Not certified: the heat-kernel coefficient 53/45 and the claim that only the opening angle at S
contributes (cited literature, no formal counterpart).

## (c) Semiclassical Einstein equations at one loop, Section 5 — core identity only

`semiclassical_c.lean`: from E⁽¹⁾[δ_Iδ_J g] = −2E⁽²⁾[δ_I g, δ_J g] (the paper's (semi:equation-variations))
it follows exactly that E⁽¹⁾[½Σ^{IJ}δ_Iδ_J g] + Σ^{IJ}E⁽²⁾[δ_I g, δ_J g] = 0, the order-ħ content of
(semi:semiclassical-einstein). Not certified: the derivation of the hypothesis from E[g(φ)] = 0 on a family
of solutions (smoothness of the solution map), the O(ħ²) remainders, conservation of the source (Bianchi
identity), the retarded solution.

## Time

Brief 16:12Z; reading 16:15Z; (a) closed 16:50Z; (b), (c) 17:05Z.
