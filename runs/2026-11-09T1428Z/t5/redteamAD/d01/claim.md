# d01 – a reader file cited twice (registry block order) + dedupe + "divided by" glue

Weakness: P11b orders the lines of each reader FILE (`idx` may not decrease) but not the BLOCKS of the registry, and a
repeated line (same idx) is accepted. `generate` drops a text contained in one already shown but still sets `prev` to it,
so the next "divided by ..." line passes the glue test and is appended to `par[-1]`, whatever that is. With CLAUSES.txt
cited twice around the one SYMBOLS line for order 2, the repeated first half of the quotient is dropped and the divisor
is glued to the order-2 symbol clause. No reader line is added or removed, no new reader file (so `roles_route` has no
added line and `registry_removals`/`baseline_reentry` see nothing); only `# source:` lines and their order change.

Generated phrase (phrases.txt, as printed in CLAIMS.md for `cosmoCoeff`):

> the cosmographic coefficient with the derivative order of the coefficient {n}, the scale factor {a} and the time of
> evaluation {t} ({n}-th time derivative of the scale factor over the scale factor; **The order 2 coefficient is minus the
> deceleration parameter usually written q divided by the {n}-th power of the Hubble rate**; orders 0 and 1 coefficients
> are one; The order 3 coefficient is the jerk parameter usually written j; ...)

False against the body `iteratedDeriv n a t / (a t * hubble a t ^ n)`: (1) the order-2 coefficient is a''/(a H^2) = -q,
not "-q divided by the n-th power of the Hubble rate"; (2) the general clause now reads a^(n)/a, with the H^n
normalisation moved onto an unrelated clause. The Lean body printed next to the phrase has the right quotient (a careful
reader can catch it; I argue the phrase is a plain false statement about an order-2 value, not a notational variant).

Rules passed (copy of the snapshot, apply.py, then explicit calls): `_controls()`, `duplicate_phrases`,
`formula_in_phrase`, `load_registry` (0 problems), `role_binding`, `coverage`, `registry_complete`, `generated()`
(0 problems; phrases.txt is `--generate` output), `head_noun` (U2); `--base` functions with the snapshot as base:
`baseline_reentry`, `registry_removals`, baseline growth: 0; `roles_route`: no added registry line (the set of lines is
unchanged), so no route requirement; LEDGER line naming `Aviles.cosmoCoeff` added (the phrase changed).
Survives P10/P11 as implemented (the template prints it). Needs only the existing readings.
