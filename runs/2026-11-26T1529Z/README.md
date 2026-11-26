# Run 2026-11-26T1529Z

**THE RESULT:** parts 2 and 3 — for the first time the trust system judged major AI-produced science it did not make, end to end, with tools that work on any outside Lean result. Verdicts (DONE / NOT DONE, every link listed): S1 Erdős 304, S2 Erdős 184, S3 van der Waerden **DONE**; target 3 (AlphaEvolve rank-48 ⟨4,4,4⟩) **DONE**; target 0 (Chandrasekaran null-cone gravity) **NOT DONE** ((a) certified as stated, scope one harmonic); targets 1 (OpenAI Navier–Stokes) and 2 (zeta zeros, 41.6% → 67.2%) **NOT DONE** pending their solution replays, statement level closed (target 2: the paper's (0,T) rate is not in the Lean). Records: `validation/EXTERNAL_S.md`, `EXTERNAL_T0.md`, `EXTERNAL_T1_T2_T3.md`, `EXTERNAL_BLOCKERS.md`.

**What can a scientist now trust without checking it themselves, that they could not before?** That the Lean statements OpenAI published for Erdős 304, Erdős 184 and the van der Waerden bound say what an independent blind reading of the claims says (kernel-checked closures), that their proofs replay in their own toolchain under two independent kernels with standard axioms; that AlphaEvolve's published rank-48 decomposition computes 4×4 complex matrix products exactly; that the Navier–Stokes and zeta Lean statements imply the claims as read blind (including the literal "67.2%"); and that Eqs. (4.33)–(4.34) of the null-cone paper hold as printed, for one harmonic. And one tool for all of it: `scripts/external/replay.sh` + `external.yml` replay any outside Lean result in its own pin.

**Weakest unchecked step:** the blind readings themselves (one Sonnet reader per claim; English → Lean is judgment); then, for targets 1 and 2, the solution replays still running on GitHub.

## Start
- 15:29Z. `EXTERNAL_LOCK` absent → this run starts the external test (instruction 11). `EXTERNAL_LOCK` written and pushed first (8c99553). LOCK was held by run 1428Z, later by 1628Z; this run wrote only its own folder, `validation/EXTERNAL_*`, `scripts/external/`, `.github/workflows/external.yml`, `validation/external_replays.txt` and records.
- Env: repo ok (add_repo not exposed; the clone was present, `git checkout -B main origin/main`). Local Lean via elan (toolchains 4.33.0-rc2, 4.34.0-rc2, 4.34.1 for the three outside pins; Mathlib caches); cargo for nanoda; two cores, ~7 GB, memcg limit ~5 GB (OOM-killed one leanchecker; fixed). Subagents: Sonnet blind readers (8), web-fetch readers, one referee.

## What we did (in order)
1. **Target S** (OpenAI math release, Erdős families, smallest Lean closures first): briefs (0be6d39) → blind readings (b9f6f85) → closures (e98ce7c) in the release's own pin; definition pins; solution closures built locally and replayed: match (challenge statement with challenge definitions, proved by the solution), `#print axioms`, nanoda on every dependency (45,753 / 41,966 / 36,021 declarations), leanchecker module by module (58 / 34 / 115 modules, 0 failures); then the same on GitHub (run 45862470764: three jobs green). Verdicts committed (1c347c7) before any review was read; then the comparison (family 159: the survey's "headline not formalized" reproduced by the coverage gate, auditor not blind).
2. **Target 0**: brief (4c1eda2) → reading → all five reader theorems proved (single-mode correlator, (4.33) series and limit, (4.34) exact G_N³ coefficient, H_N = log N + O(1), Im = −log s/s³ + O(1/s³) via an elementary Clausen estimate); finiteness does not need the chosen phase (π²/(12s²)); (b) arithmetic certified, equal to Sen's J-summed coefficient; a candidate inconsistency in (b) was withdrawn by a referee; (c) algebraic core only.
3. **Target 1**: Clay text read; brief → reading → closure frozen ⟹ reading for (C) and (D) in OpenAI's pin; zero-solution and C^∞ pins. Replay: GitHub (610 modules).
4. **Target 2**: paper TeX read; brief → reading → closure of 6/7 reader theorems incl. the literal 67.2% (decimal certified via `Complex.exp_bound`); the (0,T) rate UNCOVERED. Replay on GitHub: all 17 matched theorems with standard axioms (job 140090067980; its failure was our wrapped-output parser, fixed: `check_axioms.py`).
5. **Target 3**: data extracted with `literal_eval`, 4096 tensor entries checked by the kernel (`decide +kernel`, propext only), algorithm theorem over ℂ, reading closed 2/2.

## General fixes (annex LIV; each re-run on at least one other target)
- `scripts/external/replay.sh` + `.github/workflows/external.yml` + `validation/external_replays.txt`: closure extraction into a minimal project in the outside pin (Mathlib cache), challenge wrapped in `namespace Chal` and matched against the solution, axioms, leanchecker per module, nanoda on the export, the program's readings/closures as extra modules, advisory scan. Fixed during the run on real failures: memory (one module per leanchecker), comments mentioning `sorry`, theorems with arguments, root-level challenges, Mathlib's own dependencies, the outside project's leanOptions, wrapped axiom output.
- `scripts/external/coverage.py`: every reading theorem without a closure is UNCOVERED; a verdict is DONE only at full coverage.
- `scripts/external/scan_escapes.py` (advisory): nested Lean comments handled after a false `axiom` alarm (zeta-23 docstring), caught by comparing with the authors' audit.

## Blockers
`validation/EXTERNAL_BLOCKERS.md`.

## Next
- Read the GitHub replays of T1 (run 45872140013) and T2 (re-dispatched with the fixed axiom parser), and S4 cycle–clique (run 45862470764, job 140056834017); update the verdicts.
- Target 0 (b), (c): the blocking links are physics inputs without formal counterparts (heat-kernel coefficient; Einstein operator on a space of solutions).
- The rate O(log log T/log T) of target 2 has no Lean statement; tell the authors only through Alexander (47.1).
