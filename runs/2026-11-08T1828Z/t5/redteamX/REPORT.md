# Red team X report (phrases of pinned definitions)
All six defects edit scripts/trust/phrases.txt, append one LEDGER.md line naming the definition (the allowed disclosure), and patch CLAIMS.md best-effort (the author regenerates it). No Lean. apply.py tested on a scratch copy of the three files. Weakness exploited by all: no check compares a phrase with the body or pin theorem; check_claims.py lints only glossary terms and U1 duplicates; the --base check needs just a LEDGER mention.
| d | category | defect | generated sentence misread | expected |
|---|---|---|---|---|
| d01 | role swap | redshift phrase: "observed at time t, of light emitted at time t₀" | "the redshift a(t₀)/a(t) − 1, observed at time `t`, of light emitted at time `t₀`" | ACCEPTED |
| d02 | wrong formula | angDist phrase: d_L/(1+z) instead of d_L/(1+z)² | "the angular-diameter distance d_L/(1 + z), at observation time `t₀`…" | ACCEPTED |
| d03 | over-description | IsCriticalIsotherm phrase adds "twice differentiable" and "horizontal inflection point", "the critical point"; body is deriv=0 ∧ deriv deriv=0 (junk-compatible) | "`p` is twice differentiable at `v` and has a horizontal inflection point there" | ACCEPTED |
| d04 | understated hypothesis | IsFlatLCDM phrase drops "H₀ > 0" and "a positive" | "where H₀ = H(`t₀`), z is the redshift observed at `t₀`, and a is differentiable on that neighbourhood" | ACCEPTED |
| d05 | placeholder permutation | IsRobSolution: k₂ and k₃ exchanged in the rate equations (10^4 vs 3·10^7) | "`y₁`′ = −`1 / 25`·`y₁` + `30000000`·`y₂`·`y₃` …" | ACCEPTED |
| d06 | wrong convention | curvK phrase: "equal to Ω_k" instead of "−Ω_k" | "(c = 1; equal to Ω_k, the curvature density parameter)" | ACCEPTED |
Caveat: the CLAIMS.md patch for inline Prop-valued phrases (d04, d05) is best effort; regeneration by Claims.lean produces the final text. Possible side catches: V1/V13 vocabulary checks reading the changed phrase words (d03 adds "inflection", "differentiable"), which only affects paraphrases, not the defect.
