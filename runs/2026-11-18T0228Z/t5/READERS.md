# Three-reader test on CLAIMS.md docstrings and STATE.md's banner — run 2026-11-18T0228Z

Pre-registered in `reader_brief.md` (committed a0ebddd before any reader ran). Readers: Sonnet subagents, each alone with its file(s), not told anything was altered. Pages built by `scripts/make_reader_pages.py`. Graded by the key fixed in the brief.

## Before (pages as on main)

| reader | arm / page | `gelfand_pde_radial_many_centre` (a) | misled by | `fs_neg_reversed_wall_shear_3_exists` (a), (b) | other items vs key |
|---|---|---|---|---|---|
| r1 | A, CLAIMS clean | yes | — | yes, β = −3/100 only | `avilesL0Claim_false` (b) "particular, in a sense … as the generated text reads, it takes no parameters" |
| r2 | A, CLAIMS clean | yes | — | yes, β = −3/100 only | `avilesL0Claim_false` (b) "particular, in the sense that it is a statement about one printed formula" |
| r3 | B, CLAIMS + W + G | **no** | **W** (quoted the paraphrase's status line) | **unclear**, β = −3/100 only (G named, rejected) | — |
| r4 | B, CLAIMS + W + G | **no** | **W** | **unclear** ("leaning yes"), β = −3/100 only (G named, rejected) | — |
| r5 | B, CLAIMS + W + G | **no** | **W** | yes, β = −3/100 only (G named as overreach) | — |
| r6 | C, CLAIMS generated only | yes | — | yes, β = −3/100 only | `gelfand_extrema` (b) "particular" (equation fixed, λ = 1, dimension 3) |
| r7 | C, CLAIMS generated only | yes | — | yes, β = −3/100 only | `avilesL0Claim_false` (b) "the negation holds for particular Ω" |
| r8 | D, STATE + W′, CLAIMS clean | **no** | **W′** (noted CLAIMS has no withdrawal flag, still took W′) | yes, β = −3/100 only | — |
| r9 | D, STATE + W′, CLAIMS clean | **no** | **W′** (called CLAIMS "no withdrawal flag") | yes, β = −3/100 only | `avilesL0Claim_false` (b) "particular" |
| r10 | D, STATE + W′, CLAIMS clean | **no** | **W′** (quoted STATE's own banner "CLAIMS wins", then: "CLAIMS.md still lists the statement, with no withdrawal marker, because it is generated") | yes, β = −3/100 only | — |
| r11 | E, STATE main, CLAIMS clean | yes | — | yes, β = −3/100 only | — |

Ranges of `gelfand_pde_radial_many_centre` (lam = 2; |lam − 2| < ε(N); 2 ≤ lam < 3.321992118): correct in all 11 answers.

**Verdicts by the pre-registered rules.**
1. CLAIMS docstring label **insufficient**: W misled 3/3 (r3–r5), clean readers 0/2 on that item. G (contradicted by the generated claim) misled 0/3 on (b) — the same split as the findings page (run 2026-11-15T1628Z) — but turned (a) into "unclear" for 2/3: a contradicted paraphrase still costs a reader confidence in a valid result.
2. Generated-only page **not met as literally written**: r6 answered `gelfand_extrema` (b) "particular", r7 `avilesL0Claim_false` (b) "particular Ω" — key: all / no parameters. The same two answer shapes occur on the clean page (r1, r2 on `avilesL0Claim_false`; r9 too), so they measure the question's ambiguity on parameter-free statements, not the loss of the paraphrase; on (a) and on both ranges r6, r7 answered as the key. By the rule the paraphrases stay.
3. STATE banner **insufficient**: W′ misled 3/3 (r8–r10), control r11 not misled. Every misled reader said CLAIMS.md is silent on status: the banner sends readers to a generated page that has nothing to say about the question they are asking.

**Shape (both pages).** A hand-written status sentence wins whenever no generated line speaks about status. Labels ("not generated", "Unchecked prose … those win") do not help, because the generated page they point to is silent on the point.

**Fix chosen by rule 4 (2 fails, 1 and 3 hold): a generated status line.** `scripts/trust/Claims.lean` now prints under every headline: "**Status (generated):** proved in module … of `Checked`; axioms, computed by Lean when this page was generated: … . This status is decided by Lean and the registry `scripts/trust/headlines.txt`, never by prose: a headline is withdrawn only by removing it from `Checked` and the registry, which removes it from this page." (the axioms come from `Lean.collectAxioms`; any axiom other than `propext`, `Classical.choice`, `Quot.sound` is a blocking generator error), plus a fixed preamble paragraph. STATE.md's and README.md's banners name that line as the status of record (goal guard requires the sentence).

## After

(see below)
