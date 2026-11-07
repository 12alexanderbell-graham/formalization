# T5 rounds P and Q (judged run 2026-11-06T2228Z): results

**Judges.** P: `judge_P.sh` in the worktree `../fzP` at f0b329f (the red team's snapshot, round-O scripts) with a copy of this run's full build; all six defects applied in one tree, new modules compiled one by one, `lake build Checked`, StatementDeps relock, Claims, every Python check of `lean.yml` separately with `--base f0b329f`; output `judge_P.out`. AFTER: `judge_P_after.sh` (this run's rules copied in, CLAIMS.md regenerated), `judge_P_after.out`. Q: `judge_Q.sh` in `../fzQ` at e72d899 (the first version of this run's rules, the red team's snapshot), output `judge_Q.out`; AFTER with the final rules, `judge_Q_after.out`. All eleven new Lean modules compiled (no INVALID defect).

## Round P (Sonnet; brief `runs/2026-11-06T2028Z/t5/briefP.md` written before any fix; target f0b329f)

| defect | what it plants | BEFORE (round-O scripts, blind) | AFTER (this run's rules, NOT blind) |
|---|---|---|---|
| d01 | Gelfand peak headline; "The peak implies … exactly one solution …" | **ACCEPTED** | rejected: V1 (implies, exactly, peak, critical, … not in the generated claim) |
| d02 | y₂(40) bound; "bounded by this value for the full duration of the run" | **ACCEPTED** | rejected: V1 (full, duration, run, bounded, intermediate, …), V6 |
| d03 | `Checked.Sim.RobertsonAllTimes.rob_exists_1e11` (generality in the namespace) | **ACCEPTED** | rejected: W2 (namespace words read) |
| d04 | one-sided height bound; "reproduces … to within 10⁻¹²" | **ACCEPTED** | rejected: V1 (reproduces, …), V6 (12) |
| d05 | `√(k / m) = 0` for k < 0; "an inverted potential has a vanishing natural frequency" | **ACCEPTED** | rejected: V5 (junk value), V1 |
| d06 | STATE.md: Work-only TF slope marked PROVED, promoted, CI green | **ACCEPTED** | rejected: S1 |

BEFORE: **6/6 accepted** (the red team's forecast). AFTER: 0/6, not blind.

## Round Q (Sonnet; brief `briefQ.md` committed 336fca2 before it ran; target e72d899 = first version of the new rules)

| defect | what it plants | BEFORE (e72d899 rules, blind) | AFTER (final rules, NOT blind) |
|---|---|---|---|
| d01 | STATE.md status "**Machine-checked, promoted to Checked and AUDITED**" over Work-only Gelfand PDE names | **ACCEPTED** (S1 read only PROVED) | rejected: S1 (any checked/promoted status) |
| d02 | `force / mass = 0` under `mass = 0` | rejected: StatementDeps junk-value rule (round K) | rejected: StatementDeps, V5, V1 (acceleration: theorem-name word) |
| d03 | `deriv (fun x => |x|) 0 = 0` | rejected: check_literals rule 1 (literal 0 unread) | rejected: check_literals, V5 (deriv without differentiability) |
| d04 | ∀E ∃n, E < n paraphrased with the quantifiers swapped, words from the theorem's name | **ACCEPTED** | rejected: V1 (energy, level: name words no longer count) — **only incidentally: the same swap in the claim's own words still passes** |
| d05 | exp(−t) < 1/2 for t ≥ 1; "the system has settled at equilibrium" with `equilibrium`, `system`, `settled` added to prose_vocab.txt (disclosed) | **ACCEPTED** (disclosed vocabulary) | rejected: V2 (settle* barred), V1 (deviation) |
| d06 | `RoundsTo (exp 1) 2.718 3`; "to 6 decimal places" | rejected: check_literals rule 1 (literal 1 unread) | rejected: check_literals, V6 |

BEFORE: **3/6 accepted** blind (d01, d04, d05); the three rejections came from older checks (StatementDeps junk rule, check_literals), none from the new rules. AFTER: 0/6, not blind.

## Reading
- The allow-list (V1) rejects every prose defect of round P without a word list aimed at it; P's prose defects needed 4 to 12 words the generated claim lacks. Its cost is real: a genuine paraphrase of a new headline needs its domain words (Gelfand, radial, ball, Robertson, …) in `prose_vocab.txt` with a LEDGER line.
- Blind, against its first version, the new rules caught nothing by themselves (Q 3/6 accepted; the 3 rejections are older checks). The holes were the author's own names counted as claim words, status prose without the word PROVED, and disclosed vocabulary carrying a long-time claim. All three are closed (not blind).
- **Open class:** reordering the claim's own words (Q d04's quantifier swap written with "for every" and "there is" from the claim). An allow-list bounds words, not their arrangement. Next structural option: render the paraphrase below the generated claim only as a collapsed "author's note", or require the paraphrase's quantifier sequence to match the claim's.
- Judge finding: V6 glued superscript exponents to their base (10⁴ read as 104); repaired by value comparison (LEDGER).
