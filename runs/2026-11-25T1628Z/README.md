# Run 2026-11-25T1628Z

**THE RESULT:** parts 2/5 by rotation (STATE 3h; next step STATE 3i). The Lean theorem of this run and its statement are in section What we did.

**What can a scientist now trust without checking it themselves, that they could not before?** For the isothermal sphere, the rate of consecutive radii of the mass extrema and the rate of the mass values at every extremum, by a kernel theorem (section What we did; `CLAIMS_READER.md`).

**Weakest unchecked step:** the chain of cells of the module `Checked.Math.BEState300` (kernel data), section What we did.

## Start
- 16:28Z. `scripts/start_run.sh`: the session clone was on a stale shallow `main` (860fd46, an ancestor of origin/main); reset to origin/main 4631dbc after `git fetch --unshallow`; no LOCK (taken dd41854, 48.4).
- Env: repo ok (add_repo not exposed; the session clone was present). Local Lean v4.35.0 (elan), Mathlib cache; judge's build of 21bff96 (artifact of 45626806307) restored by streaming; `lake build Checked` replayed it (3802 jobs). Subagents: one Sonnet blind restater, one Opus referee, one Sonnet blind literal reader.
- CI: 45653611577 (4631dbc, run 1428Z's final push) in progress at start; read in section End.

## What we did

Candidate (b) of section Next of `runs/2026-11-25T1028Z/README.md`: the rate statement for a second model of the same kind.

1. **Freeze** (3d27c78): `runs/2026-11-25T1628Z/lean/BonnorEbertTurningRatio.lean`, the statement of `Checked.Math.BonnorEbertMonotone.bonnor_ebert_extrema_monotone` with two conjuncts appended, for the mass m(s) = s²(−φ(s))e^{w(s)/2}/√(4π) and its extremum sequence ξ:
   `Tendsto (fun k => ξ (k + 1) / ξ k) atTop (𝓝 (Real.exp (2 * Real.pi / Real.sqrt 7)))` and
   `Tendsto (fun k => (m (ξ (k + 1)) − √(2/π)) / (m (ξ k) − √(2/π))) atTop (𝓝 (-Real.exp (-(Real.pi / Real.sqrt 7))))`
   (the mass written out in the Lean text). Float check before the freeze (mpmath, `scripts/be_ratio_float.py`): 10.749087 and −0.305010 by k = 13. `check_freeze_name.py` ok (name and docstring; the first docstring draft's words 'rate', 'consecutive', 'quotients' were refused and replaced before the freeze commit). Briefs of the blind restatement and of the referee in the same commit.
2. **Blind restatement** (Sonnet, ≈ 30 s): `blind/BonnorEbertTurningRatioBlind.lean` — the mass and the singular value named, a two-sided derivative of φ for s > 0, the global maximum with a weak inequality, the first radius as membership in a closed interval. Closed in Lean from the program's statement in one file (`Work/Math/BonnorEbertTurningRatioBlindClosed.lean`, compiled first time).
3. **Referee** (Opus, ≈ 7 min, `referee/REPORT.md`): **STANDS**, no corrections. Its own Taylor integrator (two runs, agreement to 1e-33) gives ξ_k and m(ξ_k) to k = 15; both quotients oscillate about their limits with the error shrinking about 0.305-fold per step; it checked by hand and in sympy every step of the planned route (zeros of g = 2u − v are the extrema; at a zero the weighted norm is 32(u − 1)² and m = √(2/π)u²; the angle identity; the deviation quotient as (x_{k+1}/x_k)·(2 + x_{k+1})/(2 + x_k)). Prior art (from memory, not checked: the arXiv fetch was blocked): both constants follow from Chandrasekhar's 1939 asymptotics of the homology spiral; no formal verification known.
4. **Blind literal reading** (Sonnet, brief 86072fa committed alone first): index step 1, power 2, divisor 2, normalisation 4, singular mass 2, integer 7 → `Checked.Trust.SecondReading.beTurnRatio` (`Checked/Trust/SecondReadingBETurnRatio.lean`). The radius limit is the literal text of the reading `gelfandTurnRadii` of run 1028Z (the same limit for another sequence).
5. **Proof** (`Checked/Math/BERatioCore.lean`, `main`; no new certificates, no new cells; compiled at the second attempt of each of two lemmas):
   - the angle of `Checked.Math.GelfandRatioCore`, measured from the ray of g = 0 instead of y = 0: cosine σ(−6x − 5y)/√(8 Nw) (`fcB`, `thB`); 8 Nw = (6x + 5y)² + 7(2x − y)²; the identity 28(y − 2x) Lq = (6x + 5y) Dq − 2 Nw(6ẋ + 5ẏ) (`angB_id`, by `ring`) gives the same derivative 2√7 Lq/(Nw t) (`thB_deriv`); the sign of g' = 8u(1 − u)/t at a zero puts the angle at 0 and π at consecutive zeros (`sideB_left`, `sideB_right`); so `segB_bounds` holds with the constants of `Sys.seg_bounds` (its proof copied by string);
   - the sign of g on each segment from the monotone mass segments of `bonnor_ebert_extrema_monotone`, through u v³ = 4π m² and its derivative u v³ g / t (`P_deriv`, `P_anti_of_M`, `neg_of_antiP`, transversality `no_zero_insideB`); the extrema past radius 300000 are zeros of g (`zero_between`);
   - at a zero of g the mass is √(2/π) u² (`M_at_zero`) and Nw = 32 x², so the deviation quotient is −exp(D/2) (`q_eq32`) times (u_{k+1} + 1)/(u_k + 1), which tends to one; the limits come from `Checked.Math.GelfandRatioCore.lim_D`, `lim_q` and `Checked.Math.GelfandRadiiCore.lim_L`.
   Axioms of `main`: propext, Classical.choice, Quot.sound.
6. **Promotion**: `Checked/Math/BERatioCore.lean`, `Checked/Math/BonnorEbertTurningRatio.lean` (headline `Checked.Math.BonnorEbertTurningRatio.bonnor_ebert_turning_ratio`, statement byte-identical to the freeze), `Checked/Trust/SecondReadingBETurnRatio.lean`, `Checked/Trust/NecessityBW.lean`, `Work/Math/BonnorEbertTurningRatio.lean` (the freeze with one import and the proof added), `Work/Math/BonnorEbertTurningRatioBlindClosed.lean`, the non-vacuity witness in `Checked/Trust/Witnesses.lean` (the global regular solution), the headline in `scripts/trust/headlines.txt`, the literal readings of the parent headline plus `gelfandTurnRadii` and `beTurnRatio`.
7. **Necessity**: the hypotheses are those of `bonnor_ebert_extrema_monotone` in the same order and the conclusion contains that headline's conclusion, so `Checked.Trust.NecessityBW` carries each witness of `Checked.Trust.NecessityAN` over: 1, 3, 4 NEEDED, 2 REDUNDANT — every hypothesis classified in the promoting run.

## Measure

- Trust map: one headline added, every hypothesis of it classified on promotion, non-vacuity witness proved.
- Second model of the rate route: the analytic tail of `Checked.Math.GelfandRatioCore` carried to the Bonnor–Ebert mass by changing the reference ray of the angle; no certified number was recomputed. Pipeline cost: freeze to compiled proof about twenty minutes.
- The same deviation-quotient limit as the Gelfand parameter's (−exp(−π/√7)) for different radii, as the referee's integration confirms (the extremum radii differ: 6.45, 67.0, … against 4.07, …).

## Next
- CI read first: the run of this run's final push (new Checked modules `BERatioCore`, `BonnorEbertTurningRatio`, `NecessityBW`, `SecondReadingBETurnRatio`; `Witnesses` changed; nanoda and leanchecker re-check the new modules). Green on every job → `bonnor_ebert_turning_ratio` PROVED: the judged template in its STATE.md heading (`check_stale_status.py`) and one L.2 line to Alexander. Red → `python3 scripts/trust/records_check.py <base>` with the newest ancestor green on every job (4631dbc if its run 45653611577 ends green; else 21bff96).
- Parts 2/5 next: (a) explicit bounds for the Bonnor–Ebert rate from a named extremum on, as run 1028Z did for the Gelfand parameter: the referee's integration puts ξ 5 ≈ 907946 past the start of the small ball (300000; ξ 4 ≈ 84506 is not), and `Checked.Math.BEState300` already bounds the weighted norm there (Nw ≤ 3234/100000000, `Checked.Math.BEAllMain.N0_bounds`), so with ε ≤ √Nw(300000) ≈ 0.0057 for every later segment the segment bounds give the radius quotient in about [9.2, 12.8] and the deviation quotient in an explicit interval from k = 5 on, with no new certificate; the one missing fact is the position 300000 ≤ ξ 5 (copy the identification of the tail's first zero in `Checked.Math.BEAllMain.main`, which starts the tail sequence at 300000); (b) as (a) of section Next of `runs/2026-11-25T1028Z/README.md` (tighter Gelfand bands); (c) a field other than the isothermal-sphere family (THE RESULT part 5), if a run finds a candidate whose pipeline is shorter than (a).
- Part 1 next: as in section Next of `runs/2026-11-25T1228Z/README.md`.
- Part 3 next: as in section Next of `runs/2026-11-25T1428Z/README.md`.

## End
- (filled at the end of the run)
