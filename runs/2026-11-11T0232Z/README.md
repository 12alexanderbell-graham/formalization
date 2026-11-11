# Run 2026-11-11T0232Z (scheduled)

**THE RESULT:** parts 2 and 5 (rotation) — new certified science in fluid mechanics: **the Falkner–Skan separation value β\* (zero wall shear) is unique and lies in (−0.1988377351, −0.1988377350)**, PROVED in Work + AUDITED (two theorems, both blind restatements closed in Lean, referee STANDS) and **promoted to Checked** the same run (blind literal reading, NV witness, two necessity witnesses; every local check green); PROVED once the main CI run is green.

**What can a scientist now trust without checking it themselves, that they could not before?** The classical separation value of the Falkner–Skan family, quoted since Hartree (1937) from floating-point computations to 4–9 digits (and misprinted in the 7th–8th digit in two recent papers), now has a machine-checked ten-decimal enclosure together with a proof that no other β has a separation profile of the decaying kind.

**Weakest unchecked step behind the results:** the promotion's CI run on main is not yet read (local checks green); 16 of the 18 hypotheses of the equality theorem are not yet shown needed or redundant; the claim that no rigorous enclosure exists in print rests on one referee's limited search.

**Measure:** Work headlines +2 (+2 blind closures); certified chains 2 (260 cells, margins ≥ 2.3·10⁻¹¹); first certificate family parameterised by a coefficient of the equation (`CellProp K`) and first flow continuous in an equation parameter; axioms standard.

## Start
- 02:32Z. No LOCK (run 2026-11-11T0028Z closed it at 02:13Z). Repo pre-cloned, complete history; local main = origin/main 3e54961.
- Local Lean: elan installer accepted; Mathlib cache ≈ 3 min; `lake build Work.FSNeg.NAssemble Work.FSNeg.NCellWC Work.FalknerSkan.NegCore` ≈ 12 min.
- CI: 3e54961 (run 0028Z records, 42944553092) in progress at 02:45Z — read later.

## Target (parts 2/5): the Falkner–Skan separation value β*
- Rotation names parts 2/5. STATE item 2 proposed β = −0.15; chosen instead the separation profile (zero wall shear), listed as "not yet" since run 2026-11-07T2228Z: here a *parameter of the equation* is shot, not a start value. Scaled form F''' + K F F'' − (1 − F'²) = 0, K = 1/(−β), start (0, 0, 0): the α = 0 shot overshoots (p > 1) for K < K* and enters the forward-invariant slow region for K > K*.
- Float study (`/tmp` scripts, 45-digit Taylor integrator, bisection on the event classification): K* = 5.0292264683323215571…, **β* = −0.19883773504667754689…** (scipy DOP853 agrees to 12 digits). Events at the ten-decimal window β ∈ (−0.1988377351, −0.1988377350): Over at s ≈ 3.97, slow at s ≈ 4.08.
- Exact generator (`scripts/gen_sep_wc.py`, copy of run 0828Z's `gen_neg_wc.py` with θ = 11/15 and a mode `slowp` without a sign condition on q along the path, since q(0) = 0): Over at K = 10¹⁰/1988377351 on [0, 4] (128 cells, h = 1/32, degree 12, 10⁻¹⁸, end margin p − 1 = 2.3·10⁻¹¹) OK; SlowS at K = 10¹⁰/1988377350 on [0, 33/8] (132 cells, path margin 5.4·10⁻¹¹, end margin 7.8·10⁻¹¹) OK. Amplification e^3.6.
- Freeze: `Work/FalknerSkan/Separation.lean` (`fs_separation_exists`, `sorry`), interface `Work/FSSep/SBase.lean`.

## Work (all Lean compiled locally; commits 3e4f5c0, f6528b6)
- Forks in ONE message after the freeze (≈ 10–18 min each): A certificates (`SCellWC` by script from `NCellWC`, `SOverLo` 102 s, `SSlowHi` 120 s), B flow in K + assembly (`SFlow`, `SAssemble.core_sep`), C clamps with q(0) = 0 (`SUnclamp`), blind restater, referee + prior art. Then the uniqueness freeze (d6e6727) and forks D (uniqueness, `UCrocco`/`UCompare`/`UPair`, ≈ 10 min, the referee's route held; the start compares z² instead of η-asymptotics) and E (both blind closures, global C³ extension) + a second blind restater.
- Referee: STANDS; β* = −0.198837735046677546889047131815… by an independent method; prior art in `referee/REPORT.md` (the referee's Write was refused by the harness; the main session saved its report).

## Lessons
- Shooting in a coefficient of the equation costs no more than shooting in a start value: Grönwall for approximate trajectories (`dist_le_of_approx_trajectories_ODE_of_mem`) gives continuity in the coefficient directly, and the cell checker takes the coefficient as a rational parameter.
- A freeze of the *uniqueness* companion the same run turned an existence statement the referee called "not yet the separation value" into the full characterisation within 15 minutes, because the referee's report already contained the route.
- Fork-heavy runs: five agents in one message (three Lean forks, blind, referee) finished the whole existence proof in ≈ 30 min wall time.

## Promotion (branch `wip/sep-promo`, fast-forwarded into main)
- `promote_sep.py`; renames for the name rules: headline `fs_separation_unique` → `fs_separation_equal`, module `SeparationUnique` → `SeparationEqual` (V8 reads module names too); docstrings in the generated claim's code (V11) and without derived decimals (check_prose); `separation` added to prose_vocab.
- Blind literal reader: three briefs. The first wrote the template's denominator into the brief (B3 / brief-leak) — archived; the second brief was committed together with the staged module rename (B4) — kept as a record; the third, committed alone, passed. All three readers gave L = 1988377351, U = 1988377350.
- Necessity: fork F proved the two decay hypotheses of `fs_separation_equal` needed with the certified slow-approach solution at the window's upper end (zero wall shear, algebraic tail).
- Local: full `lake build Checked` (≈ 60 min), StatementDeps with relock (four rounds, ≈ 8 min each), Claims, every Python check of the trust and frozen steps incl. `--base 3e54961`, packet.

## Lessons (promotion)
- `git mv` stages immediately: a later `git add <one file>; git commit` carries the rename too. Before every brief or reading commit run `git diff --cached --name-only` (it must list exactly that file).
- A brief's template must not contain any numeral the reader will write, not even a denominator; give the rounding rule in words.
- V8 reads module names: name the Work module after its conclusion (`…Equal`), not its strength.
