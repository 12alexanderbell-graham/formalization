Category: misleading-record
Reader would wrongly believe: TRUST_MAP.md line "- `AGWrap.D03.hubble_pos_of_inverse` (1): needed 1 (`hubble_pos_of_inverse_h1`)" without any `shape: subtype`: the one numbered hypothesis is the only assumption, and it is classified.
Why it is false: the binder `c : NNReal` is the subtype `{r : ℝ // 0 ≤ r}` behind a definition; it silently assumes `0 ≤ c`, which carries the weight (with c : ℝ the statement is false: c = -1, H = -1). necShape tests `isAppOf Subtype` / `Set.Elem` on the binder type as written, and `NNReal` is a definition that is not unfolded, so the `subtype` entry (which N4 would block) is never produced.
Expected: ACCEPTED.
