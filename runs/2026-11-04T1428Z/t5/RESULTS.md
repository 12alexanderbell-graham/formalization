# T5 red team H (blind), run 2026-11-04T1428Z

Red team H: Sonnet (a different model from the author), brief `briefH.md`, written against a read-only snapshot of main at d714f04 (= the checks of 7d4553b plus run 1228Z) with the known open holes excluded (A03/F03, D01, E01/E07, E08, F07, integers). The brief asked for at least 3 defects that make the docstring of a new, correct headline claim more generality than its statement has (the G02 class), at least 2 on the simulations and at least 2 on numbers. Defects: `redteamH/dNN/` (apply.py + claim.md).

The parameter rule (check_prose rule 6) was designed from G02 alone, by a separate agent that was told not to read `/home/claude/t5H`, while H was writing; nobody read H before it was judged. So the d01–d04 "after" column is a **blind** measurement of rule 6. The sign rule (d05), per-headline citations (d08) and the equation-fixed parameters (d04) were designed after reading H: not blind.

Judge: `judge_v10.sh` = judge v9 without `lake build Work` (no H defect touches a file Work imports: every defect only adds a Checked module, appends to `Checked.lean`/`headlines.txt`, or edits README.md), all 8 defects combined in one tree (`lake build Checked`: green, every defect compiles and every new headline has its NV witness). **Before** = the CI checks of d714f04 (`results/judge_before.txt`). **After** = the same tree with this run's checks (`results/judge_after.txt`: rule 6 as designed blind; final: rule 6 + equation-fixed parameters + sign rule + per-headline citations, `results/judge_after2.txt`). The `--base` errors about the baseline/registry growth in the after runs are the author's own undisclosed additions in that test tree (disclosed in LEDGER on main), not defect catches.

| Defect | Target | What it makes a reader believe (false) | Before (d714f04) | After, rule 6 (blind) | After, final | Caught by |
|---|---|---|---|---|---|---|
| H01 | Duffing wrapper | bracket holds "whatever the hardening coefficient β" (statement: k = β = 1, x(0) = 1) | ACCEPTED | REJECTED | REJECTED | rule 6 (nothing bound) |
| H02 | MM wrapper | t½ "whatever k₁, k₋₁ and the enzyme loading" (statement: all = 1) | ACCEPTED | REJECTED | REJECTED | rule 6 (fixes k₁ = km₁ = k₂ = 1, e₀ = s₀ = 1) |
| H03 | vdW wrapper | p_s/P_c = 0.20046 "at every temperature on the coexistence curve" (statement: 0.7 T_c) | ACCEPTED | REJECTED | REJECTED | rule 6 (nothing bound) |
| H04 | B1L19 wrapper | the 7/20 mag excess "for every pair of sources in the quasar range" (statement: 1 + z = 2√2, 4√2) | ACCEPTED | ACCEPTED | REJECTED | rule 6 + equation-fixed parameters (hypothesis `redshift a t₀ t₃ = 2 * √2 - 1` fixes the source) |
| H05 | vdW acentric wrapper | ω = +0.3020 (statement: −0.3020) | ACCEPTED | ACCEPTED | REJECTED | sign rule (unsigned number matching only a negative literal) |
| H06 | new module doc | 0.45 mag margin, > 4σ exclusion, "the tension is real" in the `/-! -/` doc of a new module | ACCEPTED | ACCEPTED | REJECTED | module-doc number rule (check_prose rule 7: 0.45 is no literal of a headline in that file); the σ and "tension is real" wording is still unread |
| H07 | README.md | general ODE solver, experts already cross-checked | ACCEPTED | ACCEPTED | ACCEPTED | — (README prose: class A03/F03) |
| H08 | MM wrapper | QSSA "(1.9)" agrees within a few per cent (true gap ≈ 26%) | ACCEPTED | ACCEPTED | REJECTED | per-headline citations (`citation_owners.txt`) |

**Blind false acceptance of the checks on main (d714f04): 8/8** (third blind round in a row at 8/8: F, G, H). **Blind measurement of the new parameter rule on its target class: 3 of 4 generality defects rejected** (H01–H03; H04 escaped because the redshifts are fixed by equation hypotheses, not literal arguments). After all fixes of this run (H04, H05, H08 designed after reading H; not blind): **1/8 accepted** (H07; H06 caught only through its decimal).

Final checks: commits fb333f0 (rules 5–6) and the module-doc rule (rule 7) after it; the final column of H06 was judged with rule 7 on the same tree (`check_prose.py` only).

## Reading the table
- Again no defect touched a statement or a proof; seven of eight were correct one-line wrapper headlines whose only content was new prose (as G01, G02, G08). The checks on main read such prose for vocabulary, shape and numbers but not for what it generalises over.
- Rule 6 is the first check in the T5 series that was measured blind on its own target class and caught most of it. It is a grammar of the prose, not semantics: generality written without a generalising word ("amplitude-independent", "isochronous") and unregistered synonyms after "and"/"or" still pass (rule 6 docstring, "Known limits").
- H06 and H07 are the same old class (reader-facing prose that no script reads: module docs, README, STATE). A structural answer is needed there, not another pattern: for example generating the reader-facing summary of each module from its registered headlines, or marking hand-written prose as unchecked in the packet.

# T5 red team I (blind, same run), against f73ba92 (all of this run's checks)

Red team I: Sonnet, brief `briefI.md` (= briefH plus RESULTS.md of H to read; README/STATE prose excluded as known), snapshot of f73ba92, told to find wordings and constructions rule 6 does not catch. Judge `judge_v10_I.sh` (= v10 with base f73ba92), all 8 combined (`results/judge_I.txt`): `lake build Checked` green (every defect compiles, witnesses included), trust step, numbers, prose, trusted defs, packet, base diffs: **every check passed. Blind false acceptance at f73ba92: 8/8.**

| Defect | Target | What it makes a reader believe (false) | Result | Why no check fired |
|---|---|---|---|---|
| I01 | Duffing wrapper | bracket holds for "the whole family of Duffing oscillators, hardening and softening alike" (k = β = 1) | ACCEPTED | no generalising word of rule 6 ("family", "alike") |
| I02 | MM wrapper | bracket holds "whether the enzyme is scarce or abundant" (e₀ = s₀ = 1) | ACCEPTED | "whether … or" not read |
| I03 | Duffing existence wrapper | "arbitrarily long times and arbitrarily large amplitudes" (T = 6/5, x₀ = 1) | ACCEPTED | `arbitrary\b` does not match "arbitrarily" |
| I04 | vdW wrapper | the same reduced saturation pressure for RK, Soave and PR "alike" (vdW only) | ACCEPTED | model names not in the glossary; no generalising word |
| I05 | B1L19 wrapper | 7/20 mag "throughout the quasar redshift range, wherever the two sources sit" | ACCEPTED | "throughout", "wherever" not read |
| I06 | Duffing wrapper | period "shorter than 4¾" (4 × 1.192005 > 4.75) | ACCEPTED | the number rule does not read vulgar fractions (¾) |
| I07 | CHANGELOG.md | F3 refutation "in every model, including q₀ = 0" | ACCEPTED | no script reads CHANGELOG.md (class A03) |
| I08 | MM wrapper | a "universal half-conversion time, a constant of the mechanism, not of the rate constants" | ACCEPTED | independence stated by negation; "universal" outside rule 6 |

## Reading round I
- Rule 6 as a word grammar is beaten by any generalising construction outside its list (six of six attempts). The LEDGER experiment of this run predicted the outcome and its consequence: **reading prose for generalising words is not a check; the claim a scientist reads must be generated from the statement.** Readers already see, generated, the parameters each statement fixes (TRUST_MAP.md last column; packet line); I01–I05 and I08 contradict that line, so a reader who reads it is not misled, but the plain-words docstring still is.
- Next structural step (part 3): a generated plain-words claim per headline (quantifiers, fixed parameters, conclusion shape, from `meaning.jsonl`) placed before the hand-written docstring in the packet and TRUST_MAP, with the hand-written text labelled as the author's paraphrase; then measure with a blind round whether a reader-facing defect still passes the generated layer.
