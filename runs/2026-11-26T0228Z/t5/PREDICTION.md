# Closure bench — prediction, written before the bench was run (run 2026-11-26T0228Z, part 3)

Bench: `bench_body.lean` (five honest closures `R ↔ H` of real `Checked` headlines against blind readers' statements
from `Work/**/…Blind.lean`), run by `../scripts/bench_closure.sh` with the page's `closureFaults` copied verbatim.
Every bridge proves an equivalence of meaning (no side proved; only Mathlib facts and unfolding), so every
rejection is a false rejection.

Prediction:
- B1 Hiemenz existence (rcases through the reading's definitions): accepted.
- B4 Gelfand bound (rcases, a Mathlib lemma): accepted.
- B2 Hiemenz undershoot (`unfold` of the reading's definitions): rejected, through the equation lemmas that
  `unfold` generates (`….eq_def`), which are Prop-typed constants of the closure module.
- B3 Homann existence (`simp only` with the reading's definitions): unsure (run 2028Z's scratch test accepted a
  `simp only` bridge, but there the reading's module was the controls' own namespace).
- B5 B1 third coefficient (program definitions; helper lemmas `ld_pos`, `mod_iff` in the closure module):
  rejected, through the helper lemmas and through the equation lemmas of `redshift`, `lumDistFlat`, `comoving`.

Decision rule: a rule that rejects an honest bridge of a real headline because of how the author unfolded a
definition or where he put a Mathlib-only helper is a false rejection to fix, provided the fix keeps every forged
control of Claims.lean rejected and gains a forged control for each route it opens.
