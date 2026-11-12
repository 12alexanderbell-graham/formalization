# Run 2026-11-12T0227Z (scheduled)

**THE RESULT:** part 1 (trust system, T2b hypothesis necessity): **100 more hypotheses classified by machine-checked witnesses** — every one of the fourteen B1 headlines (log-polynomial luminosity-distance fits tested against flat ΛCDM: `B1`, `B1Sep`, `B1Fit`, `B1FitRL19`, `B1L19`, `B1L19Curved`) and the pinning theorems of `Checked/Fidelity/` (specification hypothesis of all twelve; every hypothesis of `hubbleSpec_pins`, `decelSpec_pins`, `yRedSpec_pins`, `omega0Spec_pins`, `curvKSpec_pins`), with no new certificate. Plus a CI repair (the previous run's push was red on one STATE word).

**What a scientist can now trust without checking:** that the B1 results do not rest on decorative assumptions: in each of them Lean shows that the source redshifts, the expansion law, the positive normalisation and (for the box theorems) every coefficient bound and the positivity at the far source are needed — a concrete model meeting every other assumption makes the claimed residual statement false — while differentiability of the scale factor and a positive Hubble rate today are implied by the others; and that the five pinned cosmological definitions above are pinned by their specifications exactly on the domain the pinning theorem states, no wider and no narrower.

**Weakest unchecked step:** the Ω-range, time-ordering and positivity-of-a hypotheses of the B1 headlines, and the coefficient/residual hypotheses of `fit_direction` and `rl19_box_unmatched`, are still open (a witness needs two-sided certified ΛCDM distance ratios or a model with Ω outside [0, 1]); this run's integration is judged by CI only from the final push.

## Start
- 02:29Z. Pre-cloned checkout detached with a stale local `main`; `git fetch --unshallow` + `git checkout -B main origin/main` = 1727c31. No LOCK; LOCK taken (dd4e46f).
- Local Lean: elan installer accepted; `lake exe cache get` ≈ 4 min; full `lake build Checked` started 02:35Z (heavy certificate modules first, serially).
- CI 43128169409 (1727c31, run 2228Z's combined push): every job green except the checked job's trust step, which failed only at `check_status_lines` S2 (the word 'global' in a STATE status line); the frozen step after it was skipped.
- Rotation: parts 1/3 due (STATE item 0); this run took part 1, the largest untouched family (B1: 180 open hypotheses, none classified).

## CI repair (31bb06c)
- STATE wording fixed; `precheck_citations.py` (the PROMPT's records precheck) now also runs `check_status_lines.py`, so one command covers both records rules (LEDGER experiment). Local: `local_frozen_step.py 89d717f` 20/20 green with the author-files `.lake` outputs of CI 43128169409 (its CLAIMS/TRUST_MAP/PHRASE_LINES/frozen.txt equal the tree's).

## Plan (bottleneck; what a yes/no changes)
- B1 family: 180 hypotheses, 0 classified. Yes = shared witnesses (one model, one generic lemma) close most of them in one run; no = record which kind resists.

## Work (scratch `lean/NecessityL.lean`, copied to `Checked/Trust/NecessityL.lean` by `scripts/promote_l.py`)
- Generic redundancies: `diff_of_law` (law with positive radicand ⇒ differentiable), `H0_pos_of_redshift` (law with H(t₀) ≤ 0 ⇒ a non-increasing ⇒ no positive redshift), flat and curved radicand positivity: hdiff and hH₀ REDUNDANT in 13 headlines (+ hdiff in `lumDistFlat_flatLCDM`).
- Redshift conditions NEEDED by moving one source onto the other (residual difference 0); `0 < H` NEEDED by `H = 0` (junk division); box theorems: `model_ratio` (exact ΛCDM at Ω = 1/5: d₅ ≤ 4 d₃ from 2 ≤ gL ≤ 9/2) + `no_rise` give every coefficient bound, the far positivity and `0 < H` (negative H) NEEDED.
- Expansion law NEEDED via the radiation-like model a = √t (H = 1/(2t), d_L = 2z exactly): L19 central/box/curved, misses z3/z7, shape miss, `lumDistFlat_flatLCDM`.
- Separation pair: each residual condition NEEDED (ΛCDM coefficients match the other residual); static model refutes `0 < H(t₀)` in `lumDistFlat_flatLCDM`.
- Pins: specification NEEDED (constant function) in all twelve; off-domain shifted definitions (`hubbleOff`, `decelOff`, `yredOff`, `omega0Off`, `curvKOff`) meet the specifications, so the domain conditions are NEEDED; differentiability REDUNDANT in `omega0Spec_pins`, `curvKSpec_pins`.
- Every witness compiled first or second time; ≈ 1 h 20 min of Lean while the full build ran.
