Category: misleading-record
Reader would wrongly believe: TRUST_MAP.md line "- `AGWrap.D05.hubble_zero_exists` (1): needed 1 (`hubble_zero_exists_h1`)" (no shape entry; counted as fully classified): the single assumption is classified.
Why it is false: `∃! t, P t` is `∃ t, P t ∧ ∀ y, P y → y = t`, two assumptions (existence and uniqueness) behind a Mathlib definition. unfoldHead unfolds only `Checked` constants, so necShape sees no `And` and partsWalk would see one atom: neither `bundled 1` nor a per-part entry is made. The conclusion uses only existence; uniqueness is decorative, yet the line reports the hypothesis as simply NEEDED and the headline as fully classified. (Any Mathlib conjunction definition behaves so: IsLeast, IsGreatest, ...)
Expected: ACCEPTED.
