# Run 2026-11-26T1828Z

**THE RESULT:** part 2/3 evidence on outside AI science (PROMPT standing instruction 11, Alexander 17:45Z: "the next run of any kind does this first"): target 0's open question — does the null-cone paper's finite graviton-pair amplitude survive the sum over angular harmonics? — settled from the whole paper and proved in Lean: under the paper's own definitions it does not. Target 0 stays **NOT DONE**; the blocker is in the outside result, not the system.

**What can a scientist now trust without checking it themselves, that they could not before?** That the finiteness of Chandrasekaran's pair amplitude ((4.33), arXiv 2611.34924) is a one-harmonic statement: with the harmonic-independent normalization the paper itself uses, every radiative harmonic adds the same nonzero amount Li₂(e^{−2i/s})/(2s²) (nonzero for every s > 0, proved), so the sum over harmonics diverges, and so does the norm of the created pair state (Lean, standard axioms, leanchecker replay).

**Weakest unchecked step:** that the Gaussian width is the same in every harmonic. The paper never states a width for any harmonic but one; the harmonic independence is read from App. D.3 ("the symplectic form (3.42b) fixes s|k||h_I|² at a given radial profile", (D.41)) and from (3.42b) having no j-dependent factor. A fresh referee reading the source alone reached the same reading and flagged the same caveat. `weighted_sum_iff` states exactly what a different reading would need (widths w_I with Σ_I w_I² < ∞).

## Start
- 18:27Z. Session clone detached at 363df8b (= origin/main); `scripts/start_run.sh` (elan installed, Lean v4.35.0, Mathlib cache). No LOCK; LOCK taken 2d33f45.
- `EXTERNAL_LOCK`: run 2026-11-26T1529Z, heartbeat 18:27Z (fresh): the external targets stay with it, except the angular-sum task, which Alexander assigned to the next run of any kind. Written here: this folder, one paragraph appended to `validation/EXTERNAL_T0.md`, one row appended to `validation/EXTERNAL_BLOCKERS.md`.
- Env: repo ok (add_repo not exposed; clone present). Local Lean (elan, 4.35.0, Mathlib cache), leanchecker. Subagent: one Sonnet referee (brief committed first, 5c6322d).

## Bottleneck
STATE 3v / PROMPT 11 "Target 0, angular sum": `EXTERNAL_T0.md` item 2 left open whether the paper's "finite amplitude" covers the sum over angular harmonics. Yes (case i) → the per-harmonic certificate extends; no → the claims page must say one harmonic, and (case iii) the divergence is proved.

## What we did
1. **Read the whole paper.** arXiv lists one version (v1, 25 Nov 2026); PDF sha256 d17cacc… (the same file run 1529Z read); LaTeX source `main.tex` (3778 lines) searched in full for angular momentum, harmonics, polarizations, variances, widths; Sections 4.2, 4.4 and App. D.3 and the symplectic form (3.42) read line by line (neither the PDF nor the source is committed: arXiv licence).
2. **Findings with page and equation** (PDF pages):
   - p. 27, (4.7) and footnote 12: the state is a product over all modes; modes are "products of angular and radial basis functions"; widths Δq_j > 0 are free, no rule given.
   - p. 33, Sec. 4.4: "we select one polarization and one real valued angular harmonic"; the variance "has the short wavelength dependence of the squared amplitude of one graviton"; (4.32) (Δq_k)² = 1/(2sk), radial index only.
   - p. 74, App. D.3, before (D.41): "For one graviton of radial frequency |k|, the symplectic form (3.42b) fixes s|k||h_I|² at a given radial profile"; (D.41) k²|h_I|² ∝ |k|/s, j(j+1)|h_I|² ∝ j(j+1)/(s|k|): one-graviton amplitude ∝ 1/(s|k|), no j; I = (j, m, p), radiative harmonics from j = 2; (D.39)–(D.44) use j only in the focusing cost and the mode count of the clock-restricted diamond space.
   - No sentence treats the sum over harmonics or polarizations. Wording broader than the computation: abstract p. 1 ("find a finite closed form expression"), introduction p. 3 ("explicitly obtain a finite result"), Sec. 4.4 last sentence p. 34 ("The sum over graviton pairs of arbitrarily short wavelength thus defines a finite amplitude at every positive G_N" — radial wavelength).
   - **Cases: (ii) and (iii) hold; (i) does not.**
3. **Lean** (`T0/angular_sum.lean`; definitions `variance`, `pairPhase`, `Li2` copied verbatim from run 1529Z's blind reading; check log `T0/angular_sum.check.log`: compiled with Lean 4.35.0 / Mathlib v4.35.0, axioms propext, Classical.choice, Quot.sound for every theorem, no sorry, leanchecker EXIT 0):
   - `card_harmonics`: the labels (j, m, p) with 2 ≤ j ≤ L number Σ_{j=2}^{L} 2(2j+1).
   - `Li2_ne_zero`: Li₂(e^{−2i/s}) ≠ 0 for every s > 0 (real part π²B₂(x), x = frac(1/(πs)), by Mathlib's Bernoulli Fourier series; where it vanishes x(1−x) = 1/6, |sin 2πx| ≥ √3/2, and the imaginary part is within π²/6 − 1 < √3/2 of −sin 2πx).
   - `harmonic_sum_diverges`: at each harmonic cutoff L the radial sum converges to (number of harmonics)·Li₂(e^{−2i/s})/(2s²); that number is nonzero; its norm → ∞ as L → ∞.
   - `pair_state_norm_diverges`: the created pair state has squared norm (number of harmonics)·π²/(12s²) → ∞: it is not in the Hilbert space, so the paper's general bound (4.30) (certified for normalizable states, run 1529Z `sewing.lean`) does not reach it.
   - `weighted_sum_iff`, `weighted_term`: with widths w_I/(2sk), the harmonic sum converges iff Σ_I w_I² < ∞.
   - Modelling step (judgment, recorded): the connected function of the summed insertion is the sum of per-mode values — the paper's own first equality in (4.33) with the mode index running over (I, k) (the j ≠ k vanishing is certified in run 1529Z's `single_mode`).
4. **Referee** (fresh Sonnet, source only, brief 5c6322d, report not steered): same answers to all four questions — no harmonic-dependent width anywhere; no treatment of the harmonic sum; (i) false, (ii) holds, (iii) holds conditionally on the harmonic-independent width, which it calls "supported only indirectly" (from (D.41) and the j-free symplectic normalization). Its one difference: it said Li₂ vanishes "only at isolated s"; the Lean proves it never does.
5. Records: `validation/EXTERNAL_T0.md` (paragraph "Angular sum, settled"), `validation/EXTERNAL_BLOCKERS.md` (row 0 (a) settled: OPEN in the outside result).

What the claims page should say: "finite for one polarization and one angular harmonic; with the paper's harmonic-independent normalization the same amplitude summed over harmonics diverges (Lean)."

Time: reading 18:30–18:38Z; Lean 18:33–18:45Z; referee 18:39–18:40Z.
