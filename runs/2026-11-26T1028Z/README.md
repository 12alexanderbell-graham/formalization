# Run 2026-11-26T1028Z

**THE RESULT:** parts 2/5 by rotation (STATE 3q; next step STATE 3r). The Lean theorem of this run and its statement are in section What we did.

**What can a scientist now trust without checking it themselves, that they could not before?** For the isothermal sphere in the ball, at every extremum of the branch parameter from index six on, how far the quotient of consecutive radii and the quotient of consecutive deviations from the singular value are from their limits: at most a constant times a power of a ratio at most 33/100, by a kernel theorem (section What we did; `CLAIMS_READER.md`).

**Weakest unchecked step:** the chain of cells of the module `Checked.Math.BEState300` (kernel data), section What we did.

## Start
- 10:28Z. The session clone was a shallow clone with a stale local `main` (860fd46, an ancestor of origin/main); `scripts/start_run.sh` reset it to origin/main ec5e4b3; no LOCK (taken de40191, 48.4).
- Env: repo ok (add_repo not exposed; the session clone was present). Local Lean v4.35.0 (elan), Mathlib cache; judge's build of abf1764 (artifact of 45791006708) restored by streaming; `lake build Checked` replayed it (3828 jobs). Subagents: one Sonnet screener (web), one Sonnet blind restater, one Opus referee, one Sonnet blind literal reader.
- CI read first: 45791006708 (abf1764, run 0828Z's final push) green on every job (goal guard, packet, changes, work, checked incl. the trust and frozen steps, leanchecker 4/4, nanoda 4/4 memoised). Nothing to promote.

## Bottleneck (and what a yes/no changes)
- Section Next of run 0428Z, candidate (a): the bands of `gelfand_turning_radii` (10.3–11.2, −0.33 to −0.28) are fixed because the error is bounded once by its value at the seventh turning point. Yes (the error shrinks by a fixed ratio per turning point, provably) → bounds at every index that shrink geometrically, an explicit rate of convergence for the Gelfand branch as for the Bonnor–Ebert mass. No → the squeeze needs a new estimate.
- Candidate (b), a field other than the isothermal-sphere family, screened first for ten minutes as run 0428Z asked (section Screen).

## Screen (candidate (b), ten minutes)
- Sonnet with web search, brief in the run's prompt (not a file): one candidate outside every family already certified. Result: **the clamped-nuclei H₂⁺ ground state** — the two-centre Coulomb problem separated in prolate spheroidal coordinates (two linked singular Sturm–Liouville problems in ξ ∈ [1, ∞) and η ∈ [−1, 1], unknowns E and the separation constant A); quantity the energy at R = 2 bohr, −0.6026342144949… Eh as reported (this is the total energy, with the nuclear repulsion 1/R = 0.5 included; the electronic eigenvalue E of the separated equations is then −1.1026342144949…: the run that takes it must check which one each table prints) (tables of 1953 and 1971, a variational value of 2006, multiprecision work 2021–22; citations in LEDGER). Prior-art search found no interval-arithmetic or computer-assisted proof of any H₂⁺ energy. Feasibility: regular singular points by Frobenius series (Taylor cells), a validated tail on [ξ₀, ∞), existence of the two-parameter root by a Miranda or interval-Newton box, ground state by node counts. Verdict GO (moderate); it confirms digits rather than refutes them. The screener's citations are from its search and memory, not checked against the tables: the run that takes it starts by reading the printed tables.
- Floating-point scratch check of the separated equations (not evidence; `screen/h2plus_float.py`, output `screen/h2plus_float_out.txt`): the lowest even separation constant of the η problem in a Legendre basis and shooting of the ξ problem from ξ = 1 give the electronic energy −1.102634214490 at R = 2 (total −0.602634214490), agreeing with the reported value to about eleven digits, and the separation constant A ≈ −0.81173 in the convention of the script's docstring: the equations as written there are the ones to freeze.
- Recorded as the first task of the next parts-2/5 run (STATE section Next; LEDGER experiment).

## What we did

1. **Freeze** (b4272fa): `runs/2026-11-26T1028Z/lean/GelfandTurningDecay.lean`, the statement of `Checked.Math.GelfandTurningRadii.gelfand_turning_radii` with one conjunct appended, `∃ c₁ c₂ q : ℝ, c₁ ≤ 47 / 100 ∧ c₂ ≤ 3 / 100 ∧ 0 ≤ q ∧ q ≤ 33 / 100 ∧ ∀ n : ℕ, |ζ (n + 7) / ζ (n + 6) − exp (2π/√7)| ≤ c₁ * q ^ n ∧ |(λ(ζ (n + 7)) − 2) / (λ(ζ (n + 6)) − 2) − −exp (−(π/√7))| ≤ c₂ * q ^ n` (λ(s) = s² e^{w(s)}); `check_freeze_name.py --file`: name, docstring and literals ok. Briefs of the blind restatement and of the referee in the same commit.
2. **Blind restatement** (Sonnet, ≈ 30 s): `blind/GelfandTurningDecayBlind.lean` — hypotheses bundled in a structure, a two-sided derivative of φ for s > 0, the branch parameter named, windows by `Icc`, the bounds with the constants themselves. Closed in Lean from the program's statement in one file (`Work/Math/GelfandTurningDecayBlindClosed.lean`).
3. **Referee** (Opus, ≈ 2 min, `referee/REPORT.md`, saved by the run from its final message): **STANDS**. Own Taylor integration in the homology variables (40 and 50 digits agree to 3e-34) to k = 15: the actual distances are below 0.4% of the bounds; ε k+1 / ε k ≈ 0.305 = e^{−π/√7}. Worst case: rate 0.3297 ≤ 0.33 (the tightest margin), |L − 2π/√7| ≤ 29.25ε, |D/2 + π/√7| ≤ 58.10ε; no gap.
4. **Blind literal reading** (Sonnet; brief 8428bc2 committed alone first, output c06d752 committed alone as written): the indices of the eighth and seventh turning points, the two numbers of the limits, the power of s and the singular value, with constants and ratio as variables → `Checked.Trust.SecondReading.gelfandDecayRadiusBound`, `gelfandDecayDevBound` (`Checked/Trust/SecondReadingGelfandTurnDecay.lean`). Passed on its first brief.
5. **Proof** (no new certificates, no new cells; `Checked/Math/GelfandDecayCore.lean`, compiled in about 30 s, first attempt):
   - `gdecay_num`: from the four segment bounds of `Checked.Math.GelfandRatioCore.Sys.seg_bounds` with error ε ≤ 1386/1000000: |L − 2π/√7| ≤ 30ε, |e^L − e^{2π/√7}| ≤ 336ε (both exponentials ≤ 11.2), half the advance of log Nw within 59ε of −π/√7, |e^{D/2} − e^{−π/√7}| ≤ 20ε (both ≤ 0.33), and e^{D/2} ≤ 33/100; `Checked.Math.BEDecayCore.exp_diff_le` reused.
   - `decay_main`: the statement of `Checked.Math.GelfandRadiiCore.radii_main` from that theorem, then its per-segment derivations (copied) with the error kept per index: at a turning point the deviation quotient is exactly −e^{D/2} (Nw = 8(u − 1)², `q_eq`), and √Nw(ζ (k+1)) = e^{D/2} √Nw(ζ k) ≤ (33/100) √Nw(ζ k), so √Nw(ζ (n+6)) ≤ (1386/1000000)(33/100)ⁿ by induction; 336 · 1386/1000000 ≤ 47/100 and 20 · 1386/1000000 ≤ 3/100. Axioms: propext, Classical.choice, Quot.sound.
6. **Promotion**: `Checked/Math/GelfandDecayCore.lean`, `Checked/Math/GelfandTurningDecay.lean` (statement byte-identical to the freeze up to the namespace; module doc in words), `Checked/Trust/NecessityCC.lean`, `Checked/Trust/SecondReadingGelfandTurnDecay.lean`, `Work/Math/GelfandTurningDecay.lean` (the freeze with one import and the proof), `Work/Math/GelfandTurningDecayBlindClosed.lean`, the non-vacuity witness in `Checked/Trust/Witnesses.lean`, the headline in `scripts/trust/headlines.txt`, the literal readings of the parent headline plus the two new constants.
7. **Necessity**: the hypotheses are those of `gelfand_extrema` in the same order and the conclusion contains that headline's conclusion, so `Checked.Trust.NecessityCC` carries each witness of `Checked.Trust.NecessityAO` over: 1, 3, 4 NEEDED, 2 REDUNDANT — every hypothesis classified in the promoting run.

## Measure

- Trust map: one headline added, every hypothesis of it classified on promotion, non-vacuity witness proved.
- An explicit rate of convergence for the Gelfand branch: at the n-th turning point after the seventh the bound is (33/100)ⁿ times 0.47 and 0.03 (at n = 4: 5.6e-3 and 3.6e-4; at n = 9: 2.2e-5 and 1.4e-6), where run 1028Z of 2026-11-25 had fixed bands. A scientist can take the quotient of consecutive turning radii or deviations of the branch parameter at any turning point past the seventh with a certified error.
- Pipeline cost: freeze to compiled proof about twenty minutes, one reader, one freeze (the LITERAL report of run 0428Z was clean before the freeze: experiment kept, LEDGER).
- Breadth: one candidate outside the isothermal family screened (section Screen) and made the first task of the next parts-2/5 run.

## Next
- CI read first: 45809568668 of this run's final push a53280d was read green on every job by this run (section End); nothing to promote. Newest ancestor green on every job: a53280d.
- Parts 2/5 next: (b) first — the H₂⁺ ground state of section Screen: read the printed tables (the 1971 table or a later one, LEDGER) for E(R) at one R, write the separated equations with conventions at the top of a Work file, emulate the Frobenius cells at ξ = 1 and η = ±1 and the tail in exact rationals before any Lean (PROMPT working note on emulating a certificate first). The isothermal family second (the Gelfand and Bonnor–Ebert rates now both have explicit constants; remaining there: tighter constants from a smaller start error).
- Part 3 next: as in section Next of `runs/2026-11-26T0828Z/README.md`.
- Part 1 next: as in section Next of `runs/2026-11-26T0628Z/README.md`.

## End
- Local: `scripts/start_run.sh`, judge's build of abf1764 restored by streaming, `lake build Checked` (3832 jobs after the promotion), StatementDeps relock (new entries only, LEDGER), `Claims.lean` (316 claims), `check_freeze_name.py --file`, goal guard, `records_check.py abf1764` (section End is written before the final push; its result is in the final commit message).
- Message to Alexander (L.2): one line after the CI read below (new PROVED headline).
- Final push a53280d; `records_check.py abf1764`: 46 commands, 0 failed.
- CI of this run's final push a53280d: 45809568668 (started 11:19Z) **green on every job** (goal guard, packet, changes, work, checked incl. the trust and frozen steps, leanchecker 4/4, nanoda 4/4), read by this run at 12:13Z: `gelfand_turning_decay` PROVED; the judged template in its STATE.md heading; L.2 line sent to Alexander.
