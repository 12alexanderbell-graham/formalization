# T5 blind round J (run 2026-11-04T2228Z): red team against the generated claims

Red team J: Sonnet, brief `briefJ.md`, snapshot 4f60172 (CLAIMS.md and its generator as first committed), 8 defects in `redteamJ/`. Target this round: make a reader of **CLAIMS.md** (generated from the Lean statements) believe something false with CI green. Judge: all valid defects combined in one tree (worktree at 4f60172), full `lake build Checked`, trust step with author relock, Claims.lean, check_claims, check_numbers, check_prose, check_trusted_defs, packet, and every `--base 4f60172` diff (same steps as CI).

| Defect | What | Checks at 4f60172 (blind) | Generated claim at 4f60172 misleads? | After the fixes of this run (designed after reading J) |
|---|---|---|---|---|
| d01 | `lcdmE` with exponent `(1/2 : ℕ)` = 0, printed `^ (1 / 2)` | CAUGHT (check_prose: docstring says "redshift", no pinned definition reached) | yes (reads as a square root) | also flagged in CLAIMS.md: numeral types printed, "⚠ TRUNCATING ℕ/ℤ ARITHMETIC" |
| d02 | `pantheonScale`, `pantheonEpoch` = `Classical.choose` of an existence theorem (Ω = 3/10), "decel = −11/20" | ACCEPTED | yes (only `Classical.choose name` shown; name suggests a fit) | the chosen objects' property is rendered ("chosen without construction, known only to satisfy: … flat ΛCDM with Ω = 3/10 …"); the name still suggests a data fit: **disclosed, not rejected** |
| d03 | `tempScale` with R = 0.08134 (digits transposed) | ACCEPTED | yes (constant visible only to an expert) | flagged: "⚠ contains decimal constants that no check compares with a source": **disclosed, not rejected** |
| d04 | MM wrapper with binders `S E P C` (product named `C`) | ACCEPTED | yes (conclusion reads as [C] crossing ½) | binders renamed by the generator after the pinned slots (`s e c p`, author's names shown): **claim reads correctly** |
| d05 | `flatLCDM_coeffs` with the matter fraction named `ΩΛ` | ACCEPTED | yes | renamed `Ω` (author's name shown): **claim reads correctly** |
| d06 | `boyleT := 2a/(Rb)` (inversion, not Boyle, temperature) | ACCEPTED | yes (meaning carried by the name) | label "not pinned, so only the formula shown is checked, not its name": **open** (class A04/B04: unpinned formulas named as physics) |
| d07 | `RoundsTo'` (one digit looser, ℕ subtraction) for the RK Ω_a | ACCEPTED | yes (lookalike of the legend's `RoundsTo`) | **REJECTED** (Claims.lean: lookalike definitions equal up to primes; also flagged truncating) |
| d08 | CPL jerk with binders `(Ω, wa, w0)` swapped | INVALID (does not compile) | — | — |

**Blind number (checks at 4f60172): 6 of 7 valid defects ACCEPTED, and all 6 make the generated claim mislead a reader.** In all 6 the generated text was literally true (every formula and every definition body was printed correctly); the falsehood rode on author-chosen names (d03, d04, d05, d06, d07), on an object picked by choice whose property was not printed (d02), or on a constant only an expert would recognise (d03). This is a change of class from rounds F–I (falsehoods in hand-written prose): the attack surface moved to names and unchecked formula bodies.

After the fixes (not blind): 1 rejected (d07), 2 now read correctly (d04, d05), 2 disclosed in the generated text (d02, d03), 1 open (d06). Open classes: names of unpinned definitions (d06, and d02's name), constants in FORMULA bodies (d03) — both need either a pin or a PRINTED classification with a second reading.
