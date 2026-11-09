# Adversary AE (Sonnet, brief BRIEF.md, snapshot 86c07c9 = P13 as first implemented): judgment

Report: returned as the agent's final message (summarised here; the agent wrote no file). Every "passes" below was
tested by AE against the snapshot's Python functions; Lean-side effects were reasoned.

| defect | move | P13 as first implemented | after repair (this run, before the first push) |
|---|---|---|---|
| d01 | U+00A0 before `CERT \| …`: Python's `strip()` counts the line, Lean's `trimAscii` skips it silently — a certificate dropped (its printed conditions vanish) or a ghost certificate for a baselined line | passes | rejected: raw-line parsing (malformed line), Z*/C* characters banned in the certificate files and the registry (`p13_chars`), Claims.lean errors on any non-comment line it does not parse; planted control |
| d02 | any Checked theorem that mentions the definition certifies any line (`lookback_second_order` for a `decel` clause) | passes | partly rejected: the theorem's docstring must quote the line and the definition must occur in its conclusion. **Open:** a new theorem whose docstring quotes the line but whose statement says less is caught only by a reader of PHRASE_LINES.md |
| d03 | certificate theorem weakened in place (same name) | passes | rejected: `--base` requires a LEDGER line naming the theorem when its generated statement in PHRASE_LINES.md changes; planted control |
| d04 a | conditions moved into the conclusion as implications (`(h → h' → P) ∧ True`) | passes | rejected: no non-dependent arrow (other than negation) in a certificate's conclusion; sign theorems split into one per half |
| d04 b | conditions moved into a subtype binder | passes | rejected: no subtype data binder |
| d04 c | a hypothesis that is an unpinned predicate is printed by name only | passes | **open** |
| d05 | existing mismatches: `decel_neg_iff` did not assume expansion; `curvK_sign` certified a sign line half of which ("minus the curvature density parameter") it does not prove; `stationary_not_critical` is one example | — | `decel_neg_iff` now assumes a′ > 0; the curvK sign line moved to baseline group A; the stationary-point line reads as "stationarity does not imply criticality", which one example proves (kept) |
| d06 | baseline group B lines that state a property: rhoM "Ω is relative to the critical density", Duffing "v₀ the initial velocity" (false for T ≤ 0), redshift "negative redshift is blueshift" | — | first two certified (`rhoM_present`, `duffing_initial` with T > 0); blueshift line moved to group A; MM/Robertson concentration lines noted (vacuous for T ≤ 0) |

Tally: as first implemented 6/6 defect classes pass; after repair 2 open (d02 residual, d04c), 4 rejected, d05/d06 corrected in the data. Not blind: the repairs were designed after reading AE.
