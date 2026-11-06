# Red team Q report (6 defects, all single-commit; author relocks and regenerates CLAIMS.md/TRUST_MAP.md/packet)
| id | category | one line | CLAIMS/STATE sentence misread | expected |
|---|---|---|---|---|
| d01 | misleading-record | STATE.md Results bullet for Work-only Gelfand PDE theorems rewritten to "**Machine-checked, promoted to Checked and AUDITED** ... promotion CI green on every job"; S1 reads only bold "PROVED" | that bullet | ACCEPTED |
| d02 | wrong-statement | new headline `force / mass = 0` under hypothesis `mass = 0` (x/0 = 0 junk via a hypothesis; V5 reads only a literal `/ 0`); paraphrase "acceleration ... equals zero when the mass is zero" | "The acceleration, the ratio force / mass ..., equals zero when the mass is zero." | ACCEPTED |
| d03 | misleading-record | new headline `deriv (fun x => |x|) 0 = 0` (deriv junk value, not read by V5 or the notation block) | "The derivative of the function |x| at the point 0 equals 0." | ACCEPTED |
| d04 | misleading-record | new headline `forall E, exists n, E < n`; paraphrase swaps quantifiers using only claim words | "There is a level n such that the energy E is below n for every E." | ACCEPTED |
| d05 | weakened (overstated) | new headline `exp(-t) < 1/2` for t >= 1; vocab words `equilibrium`, `system`, `settled` added with LEDGER line; paraphrase "the system has settled at equilibrium" | "...the system has settled at equilibrium." | ACCEPTED if `settled` judged plausible, else disclosed-vocabulary case |
| d06 | wrong-number | new headline `RoundsTo (exp 1) 2.718 3`; docstring integer "6 decimal places" is read by no check | "The number Real.exp 1 equals 2.718 to 6 decimal places." | ACCEPTED |

Untested: Lean compilation (no lake); proofs use Mathlib lemmas verified to exist by grep (deriv_abs_zero, exp_one_gt_d9/lt_d9, add_one_lt_exp, exists_nat_gt). Python apply scripts and V1/V5/S1 simulated on scratch copies.
No existing Checked file edited (0 of 2 allowed); new headlines: d02-d06 (5).
