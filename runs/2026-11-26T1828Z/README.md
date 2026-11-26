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

## Measure
- Target 0: the open blocker row 0 (a) closed as a statement about the outside result (one harmonic; the harmonic sum diverges, Lean) — one judgment link left (harmonic-independent width, inferred from (D.41)). Trust metric unchanged (no `Checked` change).
- CI repair (records check M1/M2 of `check_headline_mentions.py`, base 1a6d332): the heading of `runs/2026-11-26T1529Z/README.md` shortened to the run id (its words "external test (standing instruction 11)" outside the vocabulary would have failed the next CI run); no check changed.

## Part 1 (rotation): plan for the receding-wall witness (no Lean this run)
Section Next of run 1228Z: `fs_separation_below_printed` hypothesis 5 (p 0 = 0) needs a separation solution with p(0) < 0 whose β lies at or above −0.1988376 (the conclusion is β < −1988376/10⁷). Float scan (`scripts/scan_receding.py`, not evidence; events as `SBase`) on the scaled field from (0, −d, 0):
- d = 1/1000: K* = 5.043384 (β* = −0.198280, 5.6·10⁻⁴ above the bound); K = 5.043 over (at η ≈ 2.93), K = 5.044 slow (η ≈ 2.98): **window [5043/1000, 5044/1000]**, β ∈ (−0.198295, −0.198255). d = 1/500: K* = 5.057653; d = 1/200: K* = 5.101147 (more margin, further from the existing stack).
- Along the trajectory (d = 1/1000): p < 0 only until η ≈ 0.041; min f = −3.0·10⁻⁵; max q = 0.811.
- **Unclamping invariants for the port of `WallSep`/`BlowSep`** (the new part is p < 0 at the wall): −d ≤ p ≤ 1 (p non-decreasing while q ≥ 0); f ≥ −d (for η ≤ 1, f ≥ −dη; and p ≥ 0 from η = 1/10 on, because while p < 0 and η ≤ 1/10, q′ ≥ 1 − d² − K·dη·2 ≥ 0.98, so q ≥ 0.98η and p ≥ −d + 0.49η² ≥ 0 at η ≥ 0.046); f ≤ η (f′ = p ≤ 1); 0 ≤ q ≤ 2 by the blowing run's energy with C = −d: E = q²/2 + p³/3 − p − 2Kdp is non-increasing while f ≥ −d and 0 ≤ q ≤ 2, E(0) = d − d³/3 + 2Kd², so q ≤ 1.18 at d = 1/1000 (1.20 at d = 1/200); q > 0 on (0, ∞) as before (q′ = 1 − p² > 0 at a zero of q with p < 1). The clamps |f| ≤ η + 2, |p|, |q| ≤ 2 are never met.
- Chains: `ChainKW`-shaped certificates from (0, −1/1000, 0) at K = 5043/1000 (Over) and 5044/1000 (SlowS), generated as in `runs/2026-11-26T1228Z/scripts/gen_sep_suction.py` / `emit_sep_wall.py` with the start changed.

## Next
- CI read first: the Lean judge run of this run's final push (no `Checked` change; expect green, nothing to promote).
- External test: left to run 1529Z while its `EXTERNAL_LOCK` heartbeat is fresh (STATE 3w); target 0's claims-page sentence is in `EXTERNAL_T0.md`.
- Part 1 next: port `WallSep` to the receding start (0, −1/1000, 0) with the invariants above (generator in the style of `runs/2026-11-26T1228Z/scripts/mk_sep_wall.py`; the `conseq` block of `SUnclamp.unclampS` changes: p ≥ −d instead of p ≥ 0, f ≥ −d instead of f ≥ 0 with the η ≥ 1/10 lemma, energy bound from `BlowSep`), chains at 5043/1000 and 5044/1000, then `fs_separation_below_printed_h5` in a new `Checked/Trust/NecessityCF.lean`. Then the positivity hypotheses (section Next of run 1228Z).
- Part 3 next: as in section Next of `runs/2026-11-26T0828Z/README.md`. Parts 2/5 next: as in section Next of `runs/2026-11-26T1628Z/README.md`.

## End
- Local: elan, Lean 4.35.0, Mathlib cache; judge build of 1a6d332 restored, StatementDeps and Claims regenerated, records_check 1a6d332 (46 commands, 0 failed); `lake env lean` of `T0/angular_sum.lean` (log saved), leanchecker on its olean; float scan for part 1. No `Checked` change; no judge's build restored.
- CI read: 45867342244 (1a6d332, run 1628Z's final push) **success**; nothing to promote.
- Message to Alexander (L.2): target 0 verdict update (angular sum: one harmonic only; harmonic sum diverges under the paper's definitions), sent as a notification.
- Annex LIV: PROMPT working note (every assumption a reader lists gets a Lean answer in the same run; whole-paper search via the arXiv LaTeX source); LEDGER experiment.
