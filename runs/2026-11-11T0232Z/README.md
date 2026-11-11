# Run 2026-11-11T0232Z (scheduled)

**THE RESULT:** parts 2/5 by rotation (stub; filled in as the run goes).

## Start
- 02:32Z. No LOCK (run 2026-11-11T0028Z closed it at 02:13Z). Repo pre-cloned, complete history; local main = origin/main 3e54961.
- Local Lean: elan installer accepted; Mathlib cache ≈ 3 min; `lake build Work.FSNeg.NAssemble Work.FSNeg.NCellWC Work.FalknerSkan.NegCore` ≈ 12 min.
- CI: 3e54961 (run 0028Z records, 42944553092) in progress at 02:45Z — read later.

## Target (parts 2/5): the Falkner–Skan separation value β*
- Rotation names parts 2/5. STATE item 2 proposed β = −0.15; chosen instead the separation profile (zero wall shear), listed as "not yet" since run 2026-11-07T2228Z: here a *parameter of the equation* is shot, not a start value. Scaled form F''' + K F F'' − (1 − F'²) = 0, K = 1/(−β), start (0, 0, 0): the α = 0 shot overshoots (p > 1) for K < K* and enters the forward-invariant slow region for K > K*.
- Float study (`/tmp` scripts, 45-digit Taylor integrator, bisection on the event classification): K* = 5.0292264683323215571…, **β* = −0.19883773504667754689…** (scipy DOP853 agrees to 12 digits). Events at the ten-decimal window β ∈ (−0.1988377351, −0.1988377350): Over at s ≈ 3.97, slow at s ≈ 4.08.
- Exact generator (`scripts/gen_sep_wc.py`, copy of run 0828Z's `gen_neg_wc.py` with θ = 11/15 and a mode `slowp` without a sign condition on q along the path, since q(0) = 0): Over at K = 10¹⁰/1988377351 on [0, 4] (128 cells, h = 1/32, degree 12, 10⁻¹⁸, end margin p − 1 = 2.3·10⁻¹¹) OK; SlowS at K = 10¹⁰/1988377350 on [0, 33/8] (132 cells, path margin 5.4·10⁻¹¹, end margin 7.8·10⁻¹¹) OK. Amplification e^3.6.
- Freeze: `Work/FalknerSkan/Separation.lean` (`fs_separation_exists`, `sorry`), interface `Work/FSSep/SBase.lean`.
