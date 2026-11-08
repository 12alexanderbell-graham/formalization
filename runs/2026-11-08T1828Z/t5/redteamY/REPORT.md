# Red team Y report (phrase rules, run 2026-11-08T1828Z)
All six are phrase rewordings in scripts/trust/phrases.txt plus an allowed LEDGER line naming the definition; no Lean. Applied to a scratch copy; P1, U1 and U2 (attribution lint approximated, rests_on ignored) report no new problem for any of them.
Not run here: Claims.lean, the full lint with real rests_on data, and `--base`.

| id | category | weakness exploited | generated line | expected |
|---|---|---|---|---|
| d01 | wrong-definition | the glossary has no term for what a variable means; "conformal Hubble rate ... conformal time" keeps "Hubble rate" as first term | `hubble a t` PINNED: the conformal Hubble rate of the scale factor `a` at the conformal time `t`; by definition deriv a t / a t | ACCEPTED |
| d02 | misleading-record | P1 bans characters, not the words "is"/"minus"; a sign convention is not in the body; the sibling `omega0` clause that would expose it is dropped | `curvK`: ... it is the curvature density parameter Ω_k (true: minus Ω_k) | ACCEPTED |
| d03 | misleading-record | source equation numbers in phrases are read by no check (digits and en dash pass P1); FriedmannEq/MasterEq citations swapped | `FriedmannEq` ... Bamba et al. 2012 Eq. (11.5) ...; `MasterEq` ... Eqs. (11.1)–(11.2) | ACCEPTED |
| d04 | misleading-record | digits and "verified" in a phrase are unchecked; imports a fitted value 0.3 and a verification claim | IsFlatLCDM: ... the fitted value of the matter fraction Ω is 0.3, as verified in Aviles et al. | ACCEPTED |
| d05 | misleading-record | the phrase can promise a domain ("not defined where a′ vanishes, no claim made there"), while Lean's x/0 = 0 means claims do assert there; no rule compares phrase promises with Lean semantics | `decel` ... (not defined where the first derivative of `a` vanishes, and no claim is made there); by definition -(deriv (deriv a) t * a t) / deriv a t ^ 2 | ACCEPTED |
| d06 | wrong-definition | glossary attribution is broad: "comoving distance" is attributed to angDist, so U2 passes when angDist is called "the comoving distance" | `angDist`: the comoving distance, at observation time t₀, ...; by definition a t * transverse K (comoving ...) | ACCEPTED or DISCLOSED (body shows the factor a t) |

Note: every defect relies on rewording being allowed with a LEDGER line that only has to name the definition. No rule checks what a reworded phrase says; U1, U2 and P1 are shallow lexical lints.
