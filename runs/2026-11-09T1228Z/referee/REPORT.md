# Referee report: β = −1/10 reversed-flow existence and the attached window (run 2026-11-09T1228Z)

Opus subagent, brief `brief_referee.md`; its Write tool refused the file, so this is its returned report, condensed by the main session (verdicts and numbers verbatim).

**Verdict:** no defect that changes the truth or meaning of `fs_neg_tenth_reversed`, `fs_neg_tenth_two_decay`, `fs_neg_tenth_window`, `fs_neg_tenth_monotone_lt`. Normalisation (β-form f''' + f f'' + β(1 − f'²), adverse sign), scaling f(s) = √10·F(s/√10), q(0) = α/√10, quantifiers and non-vacuity checked; the decay clause has content (it excludes the algebraic family, q/(1 − p) → 0).

**Independent numerics** (scratchpad, outside the repository):
| Method | reversed f''(0) | attached f''(0) |
|---|---|---|
| own Taylor integrator, mpmath 40 digits, degree 30, h = 1/8, bisection on Over/Slow (and 50 digits, degree 40, h = 1/16: identical) | −0.14054621297867156710 | 0.31926975984254337012 |
| scipy DOP853 + brentq on f'(L) = 1, rtol 1e−11 / 1e−13 | −0.14054621297880 / −0.14054621297884 (L = 12) | 0.31926975984256 / 0.31926975984254 (L = 10–12) |
Both inside the windows (reversed: margins 1.2e−10 / 7.9e−11; attached: 4.3e−11 / 5.7e−11); scaled values strictly between the certified ends. Shooting with L ≤ 11 on the reversed branch gives a value just outside the window (not converged), so a naive check needs L ≥ 12.

**Route (plain words), confirmed:** Over and SlowL open (flow continuity, strict conditions, compact prefix); disjoint (prefix before η; Lemma I for the clamped field after η, no clamp active in the region); the tube covers the window exactly (|α − mid| ≤ 2·10⁻¹⁰); supremum of the Over part is a neither-point strictly inside; tube → unclamp_from (energy) → no touch → Lemma L → not-SlowL → Lemma R. The tube replaces the plan's Lemma D and rules out the p → −1 separatrix. No circularity: the chains are hypotheses of `core_lower`, discharged by the kernel-checked `chainC`s. Generators re-run (all OK; thinnest margin: SlowL end q − B > 0 at 2.3·10⁻¹¹, kernel-checked); re-emission reproduces the chain files byte for byte.

**Prior art:** arXiv 1212.5057 Table 4 (read, same normalisation), reversed branch at β = −0.1: Stewartson −0.141; Asaithambi, Auteri et al., ITM −0.140546 — consistent with the window (6 and 3 places). No printed attached-branch value at β = −0.1 found. Stewartson 1954 and Asaithambi not read.

**Defects (all documentation/provenance; status in this run):**
1. `Work/FSNeg/NAssemble.lean:14` docstring states the inverse scaling (f(η) = F(√10 η)/√10); the code is right. Not touched (run 0828Z's file; next run).
2. `emit_low.py`: docstrings of slowL/tube chains said "overshoot". Fixed; regenerated (code byte-identical).
3. `LTube.lean` docstring omitted the radius. Fixed.
4. Chain headers named run 0828Z's generator. Fixed.
5. `gen_low.py` printed a misleading "end margins" line; tube `endm` omitted g + r1 < 1 and q + B < 6/5 (Lean checks both). Fixed.
6. `NegReversed.lean` header "the reversed-flow solution" suggests uniqueness. Fixed ("a reversed-flow solution").
7. README did not describe the lower-branch work. Fixed in this run's records.
8. Process: every "green" rests on oleans built from untracked local copies under `Work/` (CI has not seen these modules). Stands until the move to Work.

Not checked by the referee: `NCellWC` internals, the NegDecay proofs, `neg_limit`, `riccati_up` (used, not re-read); primary sources. Incident: a `pip download` briefly wrote a wheel into the repository root; moved out within a minute, never staged.
