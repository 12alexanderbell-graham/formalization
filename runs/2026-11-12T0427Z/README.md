# Run 2026-11-12T0427Z (scheduled)

**THE RESULT:** (in progress) auditor role while run 0227Z holds the LOCK; target: cut the ≈ 75–100 min local `lake build Checked` that every run pays (annex LIV, root cause: every run starts in a fresh container with no build of the program's own modules) by publishing the CI build of `Checked` as an artifact a run restores; then parts 2/5 by rotation (last 2/5 run: 1828Z; since then 2028Z, 2228Z, 0227Z were part 1/3).

## Start
- 04:27Z. add_repo not exposed; pre-cloned checkout detached; `git fetch --unshallow` + `git checkout -B main origin/main` = 60a8194.
- LOCK of run 2026-11-12T0227Z (started 02:29Z, heartbeat 04:26Z, alive) → auditor role (48.4): writes only in this folder, a `wip/` branch that touches no file of main, and a CHANGELOG append.
- Local Lean: elan installer accepted; Mathlib cache ≈ 3 min; full `lake build Checked` started 04:37Z (certificate modules first, serially, as run 2228Z advises).

## Parts 2/5: Bonnor–Ebert critical sphere (frozen in auditor role)
- Bottleneck: the program has no certified result in astrophysics, and the constants of the most used stability criterion for dense cores (ξ_max, ρ_c/ρ_0, M_BE) are quoted in print with differing digits (6.45/6.5; 14.0/14.04/14.1; 1.18/1.182) and, as far as known, never enclosed rigorously. The Gelfand stack (`Checked/Math/G*.lean`) already integrates the same equation (w = −ψ) with certified cells to s = 4.1. A yes (certified window) gives a new certified physical constant and settles which printed digits are right; a no (window false) would mean a transcription or modelling error to find.
- Key identity: m ∝ s² (−w') e^{w/2}, so dm/ds = e^{w/2} s² (e^w − w'²/2): the critical point is where w'² = 2e^w (no second derivative needed).
- Floats (mpmath, 30 digits, this run): ξ₁ = 6.45075144417, ρ_c/ρ = e^{−w} = 14.0420320486, m = 1.18222658850 (√(4π)·m = 4.19088413886); the next sign change of dm/dξ is beyond ξ = 60.
- **FROZEN** `runs/2026-11-12T0427Z/lean/BonnorEbert.lean` (`Work.Math.BonnorEbert.bonnor_ebert_critical`, compiled with `sorry` only): for every S ≥ 7 and every regular solution on [0, S] (hypotheses exactly those of `Checked.Math.Gelfand.gelfand_ball_critical`), m increases strictly on [0, ξ₁], decreases strictly on [ξ₁, 7], ξ₁ ∈ [6.4507514, 6.4507515], m(ξ₁) ∈ [1.1822265, 1.1822266], e^{−w(ξ₁)} ∈ [14.042032, 14.042033]. Moves byte-identical to `Work/Math/BonnorEbert.lean` once the LOCK is free.
- Briefs committed with the freeze, before launch: blind restatement (Sonnet), referee (Opus), printed-values screen (Sonnet).
