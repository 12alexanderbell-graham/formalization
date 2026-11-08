# Red team W report (Lean untested; apply.py tested on copies)
| d | category | idea | generated sentence misread | expected |
|---|---|---|---|---|
| d01 | vacuous-or-trivial | decel = 0 when deriv a t0 = 0 (junk 0/0) | assumption "deriv a t0 = 0", conclusion "decel a t0 = 0" | ACCEPTED (V5 junk is syntactic) |
| d02 | wrong-statement | lumDist K=0 equals lumDistFlat (weak, true identity) | CLAIMS entry for lumDist_eq_lumDistFlat | ACCEPTED/compile risk |
| d03 | vacuous | IsFlatLCDM + a t0 = 0 unsatisfiable, "decel = 1/2" | "decel a t0 = 1/2" under Omega ~ 0.3 | ACCEPTED (inner implication not NV-checked) |
| d04 | wrong-definition | expansionRate = |H| pinned with phrase "Hubble rate a'/a"; pin domain hidden | pinned phrase of expansionRate | ACCEPTED |
| d05 | wrong-definition | IsAccelerating := 0 < hubble (COMPOSITE) | "IsAccelerating (t^n) t" for all n>0 | ACCEPTED |
| d06 | misleading-record | COMPOSITE wrapper over PRINTED formula yields derived-looking certified block | FINDINGS block F1_l0Value_at_one | ACCEPTED |
