# CHANGELOG (append-only, one entry per run)

## 2026-10-30, setup (chat session)
- Created the repository layout, governance files, Lean skeleton and CI workflow.
- Reassembled Alexander's original constitution from five uploaded parts; SHA-256 4a34f9846fafce3b5d760d4b1dcec37eebe21247604666d48eb0a7ae86bc394e matches the hash in his v2.0 file.
- CI never run yet. Local Lean install refused by the environment.
- CI judge set up and proven: green on main (run 40967111191); positive controls on `control/sorry-in-checked` and `control/axiom-in-checked` failed as required, both caught by axiom-audit. nanoda report-only (format mismatch). S1 done.
- Scheduled task "Formalization run" created: every 2 hours (12 runs a day), cloud only.

## 2026-10-30T0028Z (scheduled run)
- Env: repo ok; local Lean installed via elan (works); CI runs 40981530819, 40982411889 green.
- S2 done: TARGETS.md built (8 candidates); target 1 = cosmographic expansions.
- PROVED + AUDITED: `Checked.Cosmography.lookback_second_order` (o(z²)) and `..._bigO` (O(z³)); blind restatement derived verbatim.
- Literature screen: 4 candidate coefficient errors (unverified) in FINDINGS.md.
- Message to Alexander: target pick (L.2).

## 2026-10-30T0220Z (scheduled run)
- Env: repo ok; local Lean via elan ok; local build of lean4export/nanoda refused by the environment (used CI). CI runs 40994124990, 40995247069, 40996176398, 40996270496 green; later runs in STATE.
- Typeset verification of C1–C4: all four confirmed as printed (rendered PDFs).
- **First verified finding F1** (Aviles et al. 2012 Eq. 15, ΛCDM l₀/m₀ misprint, repeated in a 2014 paper; the papers' numbers are unaffected). PROVED + AUDITED in Checked: general flat ΛCDM coefficients q₀…m₀ and refutations of the printed l₀ (every Ω ∈ (0,1] ) and m₀. Blind restatement derived; referee STANDS-WITH-CORRECTIONS.
- nanoda repaired (pinned lean4export v4.35.0 + nanoda_lib master) and made blocking again.
- PROMPT.md: Alexander's no-approval instruction; typeset route; proof-generation note.
- Message to Alexander: verified finding F1 (L.2).
