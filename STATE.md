# STATE

Last updated: 2026-10-30, run 2026-10-30T0028Z (scheduled).

## Phase
S1 DONE. S2 DONE (this run). Now: work target 1.

## Target 1: Cosmography — low-redshift (Hubble-series) expansions in FLRW
Case and ranking: `TARGETS.md` #1. The eight items (annex 36.5):
1. **Exact problem:** the model-independent expansions of lookback time, comoving distance χ, luminosity distance d_L and angular-diameter distance d_A in powers of the redshift z (and y = z/(1+z)), with coefficients in H₀, q₀, j₀, s₀, l₀ and spatial curvature; and the published versions of these coefficients.
2. **Intended checkable result:** Lean theorems (`Checked`) giving each coefficient with explicit smoothness hypotheses and remainder; Lean-certified verdicts on published coefficient tables.
3. **Who benefits:** cosmographers fitting supernova/BAO data with these series; Physlib (two open TODOs in `Cosmology/FLRW/Distances.lean`); teachers of the Hubble law.
4. **Why present methods are insufficient:** coefficients are derived by hand or CAS and copied between papers; nothing is machine-checked; hypotheses (derivatives needed, asymptotic vs convergent) are rarely stated.
5. **Strongest current evidence:** Visser's series agree with an independent sympy derivation to z⁴; a screen of 9 papers flagged 4 with candidate coefficient errors (`FINDINGS.md`, unverified).
6. **Proof obligation / falsifier:** each coefficient is either proved in Lean or a printed coefficient is refuted in Lean on an explicit model (de Sitter, Einstein–de Sitter).
7. **First decisive bottleneck:** now that the pipeline works, whether the screen's candidate discrepancies survive typeset-text verification (transcription via summariser is the main alternative explanation).
8. **Ethics/misuse:** none beyond 47.1/47.2 (never contact authors; drafts only; Alexander decides).

## Results (statuses, annex XXXVIII)
- **PROVED** `Checked.Cosmography.lookback_second_order`: t₀ − t = H₀⁻¹(z − (1 + q₀/2)z²) + o(z²), a differentiable near t₀, a′ differentiable at t₀, a(t₀) ≠ 0, H₀ ≠ 0. CI 40981530819 and 40982411889 green; audit `runs/2026-10-30T0028Z/audit.md`.
- **PROVED** `Checked.Cosmography.lookback_second_order_bigO`: same with O(z³) under C³ (the blind restater's reading; its verbatim statement is derived, `Blind.lookback_expansion`). CI 40982411889 green; same audit file.
- axiom-audit (run 40982411889): 12 declarations under `Checked`, all within [propext, Classical.choice, Quot.sound]. leanchecker passed. nanoda: still fails to parse the export ("invalid digit found in string"), report-only.

## Environment (this run)
- Repo reachable; push verified (remote head = local).
- **Local Lean works**: elan installer ran fine this run (`curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain none`, then `lake exe cache get`, ~3 min). Full build ~1 min. Use it; CI is the judge.
- Physlib clone used for reading only; not a dependency. Decision: stay Mathlib-only, mirroring Physlib's definitions verbatim (`hubble`, `decel`, `redshift`), until preparing a contribution (then bridge to `Time`/`FLRW`).
- Checked files: import specific Mathlib modules, not `import Mathlib` (full import made the nanoda export step take > 10 min).

## Daily review (53.3), 2026-10-30
- AUDITED + PROVED gained in last 24 h: 2 (the two lookback theorems). Findings: 0 verified, 4 candidates.
- Bottleneck: candidate verification (new this run).

## Known gaps
- nanoda report-only (lean4export/nanoda_lib format mismatch). **Must be repaired before any finding is reported** (STATE rule from setup).

## Open questions for Alexander
None.

## Exact next step
1. Verify the text of candidates C2 (Aviles et al. 2012 Eq. 15) and C3 (Capozziello–Cardone–Salzano 2008 Eqs. A2, A5) from the typeset source, not a summariser: try WebFetch on the arXiv listing/PDF asking for the equation verbatim from two routes, and the arXiv "v" history for corrected versions; search for errata. Why: these decide whether the program has its first finding; a negative (transcription error) removes them cheaply.
2. For each candidate that survives: freeze the paper's claim as a Lean statement, and prove the refutation on Einstein–de Sitter (C2: ΛCDM with Ω_m = 1 gives l₀ = 35/2; printed formula gives −19/2) or de Sitter (C3).
3. Repair nanoda (pin a lean4export revision compatible with nanoda_lib `debug`), required before reporting.
4. If no candidate survives: milestone 2 = d_L = (c/H₀)[z + ½(1 − q₀)z² + o(z²)] with Physlib's r = S_k(χ).
Blocking: nothing.
