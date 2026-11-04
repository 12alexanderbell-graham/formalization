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
