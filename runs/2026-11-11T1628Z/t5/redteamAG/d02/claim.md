Category: misleading-record
Reader would wrongly believe: TRUST_MAP.md line "- `AGWrap.D02.flatLCDM_hubble_pos_at` (1): needed 1 (`flatLCDM_hubble_pos_at_h1`)" (no shape entry; counted in "headlines with every hypothesis classified"): all assumptions of the headline are classified.
Why it is false: hypothesis 1 is `∀ s, s = t₀ → IsFlatLCDM Ω a s`, a conjunction (the 4-part flat-LCDM law) behind a program definition under a `∀`/implication. necShape flags `bundled i` only when the unfolded hypothesis itself is an `And`, so the `∀`-headed bundle gets no `bundled` flag and no part is classified; only the whole is shown NEEDED, while the conclusion uses just the conjunct 0<H0.
Expected: ACCEPTED.
