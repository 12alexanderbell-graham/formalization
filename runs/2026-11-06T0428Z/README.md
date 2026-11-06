# Run 2026-11-06T0428Z (scheduled)

**THE RESULT:** part 1 (every link machine-checked: rigorous simulators) by rotation (part 1 idle three runs): the simulator cannot handle stiff systems — its Grönwall bound grows like e^{Lt} with the full Lipschitz constant L, which for a stiff chemical network (Robertson: rate constants 0.04, 10⁴, 3·10⁷) is ≈ 10⁴ and makes every certified step microscopic. Step this run: a one-sided-Lipschitz (logarithmic-norm) enclosure theorem in Lean, so the error bound grows only with the largest *expansion* rate, plus the feasibility numbers for Robertson.

**What can a scientist now trust without checking it themselves, that they could not before?** (filled at the end)

**Measure:** (filled at the end)

**Weakest unchecked step:** (filled at the end)

## Start
- 04:27Z: no LOCK; pre-cloned checkout detached; `git checkout -B main origin/main` = 1b584f7 (CI 42158536757 green; 42155130561, 42150630881 green: all pushes of run 0228Z green).
- 04:30Z: elan installer worked (local Lean 4.35.0); Mathlib cache fetched.
