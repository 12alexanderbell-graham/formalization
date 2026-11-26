# Run 2026-11-26T0428Z

**THE RESULT:** parts 2/5 by rotation (STATE 3n; next step STATE 3o). The Lean theorem of this run and its statement are in section What we did.

**What can a scientist now trust without checking it themselves, that they could not before?** For the isothermal sphere, at every extremum of the mass from index five on, how far the quotient of consecutive radii and the quotient of consecutive deviations from the singular value are from their limits: at most a constant times a power of a ratio at most 21/50, by a kernel theorem (section What we did; `CLAIMS_READER.md`).

**Weakest unchecked step:** the chain of cells of the module `Checked.Math.BEState300` (kernel data), section What we did.

## Start
- 04:28Z. The session clone was a shallow clone with a stale local `main` (860fd46, an ancestor of origin/main); reset to origin/main 3e4981b, then `scripts/start_run.sh`; no LOCK (taken 2be51d3, 48.4).
- Env: repo ok (add_repo not exposed; the session clone was present). Local Lean v4.35.0 (elan), Mathlib cache; judge's build of 3a7afbb (artifact of 45734700171) restored by streaming; `lake build Checked` replayed it (3815 jobs). Subagents: one Sonnet blind restater, one Opus referee, two Sonnet blind literal readers.
- CI read first: 45752585104 (9b07719, run 0228Z's final push) green on every job (goal guard, packet, changes, work, checked incl. the trust and frozen steps, leanchecker 4/4, nanoda 4/4 memoised). Nothing to promote.

## Bottleneck (and what a yes/no changes)
- Section Next of run 2228Z, candidate (a): the bands of `bonnor_ebert_turning_bounds` are fixed (9.2–12.9, −0.42 to −0.21) because the error is bounded once by its value at the start of the small ball. Yes (the error shrinks by a fixed ratio per extremum, provably) → bounds at every index that shrink geometrically, an explicit rate of convergence, from the route already proved. No → the squeeze needs a new estimate.

## What we did

1. **Freeze** (336fc72): `runs/2026-11-26T0428Z/lean/BonnorEbertTurningDecay.lean`, the statement of `Checked.Math.BonnorEbertTurningBounds.bonnor_ebert_turning_bounds` with one conjunct appended, bounds (23/10)(21/50)ⁿ and (3/20)(21/50)ⁿ at index n + 5; `check_freeze_name.py` ok. Briefs of the blind restatement and of the referee in the same commit. **Freeze v2** (e9a7f8e, form only, before any reader was registered): the same bounds as `∃ c₁ c₂ q : ℝ, c₁ ≤ 23 / 10 ∧ c₂ ≤ 3 / 20 ∧ 0 ≤ q ∧ q ≤ 21 / 50 ∧ ∀ n : ℕ, |ξ (n + 6) / ξ (n + 5) − exp (2π/√7)| ≤ c₁ * q ^ n ∧ |(m(ξ (n + 6)) − √(2/π)) / (m(ξ (n + 5)) − √(2/π)) − −exp (−(π/√7))| ≤ c₂ * q ^ n` (equivalent): the first literal brief had to state 23/10, 3/20, 21/50 to its reader, and `check_brief_leak.py` rejected it.
2. **Blind restatement** (Sonnet, ≈ 30 s): `blind/BonnorEbertTurningDecayBlind.lean` — the mass and the singular mass named, a two-sided derivative of φ for s > 0, the global maximum by `IsMaxOn`, both bounds with the explicit constants. Closed in Lean from the program's statement (v2) in one file (`Work/Math/BonnorEbertTurningDecayBlindClosed.lean`).
3. **Referee** (Opus, ≈ 3 min, `referee/REPORT.md`, saved by the run from its final message): **STANDS**. Own Taylor integration (dps 25 and 45 agree to 4e-23; scipy cross-check) to k = 13: the actual distances are below 0.07% of the bounds; ε k+1 / ε k ≈ 0.305 = e^{−π/√7}. Worst case in interval arithmetic: the ratio 0.4136 ≤ 0.42; 400ε (margin 0.6%) and 26ε close; the 26ε step fails with the factor e^{−π/√7}e^{62ε} and closes with a common upper bound 0.4155 of both exponentials (what the proof uses).
4. **Blind literal reading** (Sonnet; first brief 3bed382 and reading 229cedf left unused; second brief 14f9748 committed alone first, output 9c6e44f committed alone as written): the indices of the seventh and sixth extrema, the two numbers of the limits and the mass formula, with constants and ratio as variables → `Checked.Trust.SecondReading.beDecayRadiusBound`, `beDecayDevBound` (`Checked/Trust/SecondReadingBETurnDecayB.lean`).
5. **Proof** (no new certificates, no new cells; `Checked/Math/BEDecayCore.lean`, compiled in about 30 s):
   - `decay_num`: from the four segment bounds of `Checked.Math.BERatioCore.Sys.segB_bounds` with error ε ≤ 57/10000 and |u − 1| ≤ ε/5 at both ends: |L − 2π/√7| ≤ 31ε, |e^L − e^{2π/√7}| ≤ 400ε, half the advance of log Nw within 62ε of −π/√7, the deviation quotient within 26ε of −e^{−π/√7}, and e^{ΔlogNw/2} ≤ 21/50; `exp_diff_le`: |eˣ − eʸ| ≤ M|x − y| when both are at most M.
   - `decay_main`: the statement of `Checked.Math.BEBoundsCore.bounds_main` from that theorem, then its per-segment derivations (copied) with the error kept per index: √Nw(ξ (k+1)) = e^{ΔlogNw/2} √Nw(ξ k) ≤ (21/50) √Nw(ξ k), so √Nw(ξ (n+5)) ≤ (57/10000)(21/50)ⁿ by induction; 400 · 57/10000 ≤ 23/10 and 26 · 57/10000 ≤ 3/20. Axioms: propext, Classical.choice, Quot.sound.
6. **Promotion**: `Checked/Math/BEDecayCore.lean`, `Checked/Math/BonnorEbertTurningDecay.lean` (statement byte-identical to freeze v2 up to the namespace; module doc in words), `Checked/Trust/NecessityCA.lean`, `Checked/Trust/SecondReadingBETurnDecayB.lean`, `Work/Math/BonnorEbertTurningDecay.lean` (freeze v2 with one import and the proof), `Work/Math/BonnorEbertTurningDecayBlindClosed.lean`, the non-vacuity witness in `Checked/Trust/Witnesses.lean`, the headline in `scripts/trust/headlines.txt`, the literal readings of the parent headline plus the two new constants.
7. **Necessity**: the hypotheses are those of `bonnor_ebert_extrema_monotone` in the same order and the conclusion contains that headline's conclusion, so `Checked.Trust.NecessityCA` carries each witness of `Checked.Trust.NecessityAN` over: 1, 3, 4 NEEDED, 2 REDUNDANT — every hypothesis classified in the promoting run.

## Measure

- Trust map: one headline added, every hypothesis of it classified on promotion, non-vacuity witness proved.
- An explicit rate of convergence: at the n-th extremum after the sixth the bound is (21/50)ⁿ times the band of run 2228Z's order (2.3 and 0.15 at n = 0; 0.07 and 0.005 at n = 4; 9e-4 and 6e-5 at n = 9), where run 2228Z's bands stayed fixed. A scientist can take the quotient of consecutive radii or deviations at any extremum past the sixth with a certified error, without an asymptotic argument of their own.
- The referee's integration puts the true distances three orders of magnitude inside the bounds (the true ratio is about 0.305, the proof's 0.42): tighter constants need a smaller start error, not a new route.
- Pipeline cost: freeze to compiled proof about fifteen minutes; the second freeze and second reader cost about ten minutes (now flagged at freeze time, section Annex LIV below).
- Annex LIV: `scripts/trust/check_freeze_name.py --file` reports numerals beside a power of a variable (LITERAL), the root cause of the second freeze; PROMPT working note; LEDGER experiment.

## Next
- CI read first: the run of this run's final push (new Checked modules `BEDecayCore`, `BonnorEbertTurningDecay`, `NecessityCA`, `SecondReadingBETurnDecayB`; `Witnesses` changed; nanoda and leanchecker re-check the new modules). Green on every job → `bonnor_ebert_turning_decay` PROVED: the judged template in its STATE.md heading (`check_stale_status.py`) and one L.2 line to Alexander. Red → `python3 scripts/trust/records_check.py <base>` with the newest ancestor green on every job (9b07719).
- Parts 2/5 next: (a) the same rate for the radial Gelfand branch parameter (`Checked.Math.GelfandRadiiCore`, from index six on: the same squeeze, `GelfandRatioCore.Sys.seg_bounds`); (b) a field other than the isothermal-sphere family (THE RESULT part 5) — the isothermal family has now had seven consecutive parts-2/5 runs; a run that picks (a) should first spend ten minutes screening one candidate for (b) and record it.
- Part 1 next: as in section Next of `runs/2026-11-26T0028Z/README.md`.
- Part 3 next: as in section Next of `runs/2026-11-26T0228Z/README.md`.

## End
