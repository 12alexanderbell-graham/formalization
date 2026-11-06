# New trust checks after round M (run 2026-11-06T1028Z), written blind to red team N

I wrote these checks from the brief `brief_checksN.md`. I worked only in `/home/claude/fzW` (detached at 6fc653c). I did not
open, list or grep anything under `/home/claude/t5N`, `/home/claude/fzN` or `/home/claude/formalization` other than
the brief, and I read no `apply.py` or `claim.md`. I read:
- the PROMPT working notes from "Definition fidelity" onwards;
- the first two bullets of STATE's "Trust track status";
- round M's RESULTS and new_checks;
- the LEDGER entries of runs 0228Z and 0628Z;
- the workflow, the `check_*.py` scripts and the registries.

I did not run lake or lean. I edited nothing under `Checked/`, `Work/`, `runs/` or `governance/`, and no records. I
committed nothing.

The existing scripts are **unchanged**: the five new scripts import them and only add restrictions.

## Rules

### 1. `scripts/trust/check_literal_targets.py` (limits 1 and 2)
This script re-classifies every literal that `check_literals.py` exempts by (a2) or covers by a binder-free closed reader
constant (value mode).
- **T1, one-number targets.** A side of `= ≤ < ≥ > ∈` in a positive position of the conclusion is a certified target
  only if it is ONE number. Allowed forms:
  - a numeral, a decimal, or a quotient `a / b`;
  - `m * 10 ^ k`, `m / 10 ^ k` or `10 ^ k`;
  - a power `(q) ^ n` of one number;
  - any of these with a sign, parentheses or an ascription;
  - `Set.Icc/Ico/Ioc/Ioo e₁ e₂` with each end one number.

  `2 < 0.480 + 1.574 * 1 + 0.176 * 1 ^ 2` now leaves 6 literals uncovered: only the `2` is a target. Exception: an
  additive term covered by a reader constant registered with slot `target` is removed first, and at most one number may
  remain. So `printedY3 + 1 / 10 ^ 14 < y₃ T` works once `printedY3` is read.
- **T2, position-bound value mode.** A closed reader constant covers a literal only at the slots listed for it in
  `scripts/trust/literal_slots.txt`. A slot is either:
  - `Def.param`: the explicit argument `param` of a call of the reached program definition `Def`. The argument index
    comes from `Def`'s explicit binders in its source, and the value must also appear for that definition and parameter
    in meaning.jsonl `fixed` (the elaborated statement).
  - `target` (see T1).

  A tuple constant names one slot per component, all in the same call. `robT` now covers the `40` passed as
  `IsRobSolution.T`, but not `y₂ 40` and not a bound `< 40`. Swapping k₁ and k₂ in the call covers neither.
  Formulas with binders keep the token match of check_literals.
- **T3.** The extra literals of each headline (passing under check_literals but not under T1/T2) must equal its line in
  the shrink-only `scripts/trust/literal_target_baseline.txt`. A registered slot that covers nothing fails.
- **T4 (`--base`).** The baseline only shrinks (subsequence rule as in check_literals). A new or changed slot line needs
  a LEDGER addition naming the constant.

### 2. `scripts/trust/check_reader_frozen.py --base` (limit 3)
- **F1.** Every non-generated `Checked/Trust/SecondReading*` or `SecondFormulation*` module that exists at the base is
  unchanged apart from its `/-! -/` module doc: no declaration or docstring added, removed or edited.
- **F2.** Every runs/ `.lean` file that is a reader file at the base is byte-identical now. A reader file is one that is
  code-identical to a base second module, or sits in a folder holding a `*brief*.md`. Deleting it is allowed only if no
  Checked module still copies it.
- **F3.** A second module added since the base that copies a runs/ file which existed at the base must copy it as it
  was at the base.

A new reading therefore needs a new reader file with its own brief, so check_blind_route B1–B4 apply to it.

Tested in a scratch clone: appending `robExtra` to `SecondReadingRob.lean` and to its runs/ copy in one commit **passes
check_provenance and check_blind_route, and fails F1 and F2**.

### 3. `scripts/trust/check_brief_leak.py --base` (limit 4, extends B3)
This reads every brief in the folder of each reader file that is new since the base. The answer values are:
- B3's numbers;
- every decimal and every integer of 3 or more digits in the reader code;
- the exact value of every closed constant body (`10 ^ 11`, `3 * 10 ^ 7`), except integers with |v| < 10.

The rules:
- **L1 (words).** Spelled-out English numbers are evaluated: cardinals, hundred to trillion, `point` plus digit words,
  minus/negative, hyphenated forms, and "X to the (power of) Y" / "ten to the eleventh".
- **L2 (split digits and notation).** Digit groups joined by at most 2 separator characters are read as one number:
  space, comma, hyphen, underscore, apostrophe, period, middle dot, thin space or no-break space. Notation `a × 10^b`,
  `a·10^b`, `10^b`, superscripts and `aEb` is evaluated.
- **L3 (fragments).** No substring of 3 or more digits of a reader numeral's significant digits may occur in a brief
  digit string. Trivial fragments are exempt: one repeated digit, or a digit followed only by zeros.

Tested in the scratch clone: a route whose brief says "one point five seven four … 1 574 … 9 999 999 791 … ten to the
eleventh" **passes check_blind_route and fails L1, L2 and L3**.

The three genuine literal-reader briefs (kappa, Robertson, ROBER long) are clean.

`--all` replays every reader folder:
- `runs/2026-11-05T0828Z/blind/briefB.md` hits 11 and 27. The 27 is a formula handed over (`27Ω²/2`); the 11 is a list
  number.
- `runs/2026-11-05T1028Z/blind/briefM.md` hits 2.4, the prior standard deviation handed over by design.

These are older formulation briefs and are not affected, because only routes new since the base are checked.

### 4. `scripts/trust/check_source_variants.py` (limit 5)
- **V1 (normalised matching).** The prose is normalised: case and diacritics; hyphens, dashes, `&`, `+`, `/` and "and"
  removed; possessives dropped; camelCase and `_` split. It is then matched against the aliases in
  `scripts/trust/source_aliases.txt`. Examples:
  - "Peng and Robinson", "van-der-Waals", "RKS", "Cattoen", "pr76";
  - acronyms PR/PR76/PR78/SRK/RKS/RK/vdW/CPL/ROBER;
  - 11 new keys with backing `source`: Stryjek–Vera/PRSV, Patel–Teja, Twu, Mathias–Copeman, Carnahan–Starling,
    Berthelot, Dieterici, Lee–Kesler, BWR, Bari test set (Mazzia/Magherini), Hairer–Wanner.

  The `printed` and `equation-number` regexes are matched as before.
- **V2 (strict `source`).** A name is backed by either:
  - a reached PRINTED or CLAIM definition that names it; or
  - a reading registered for **this** headline with `source=` that name, where at least one of its constants carries the
    name in its docstring or module doc in the **blind reader's own runs/ file**. The Checked copy does not count,
    because its docs can be rewritten.
- **V3 (strict `reading`).**
  - "printed" needs a registered constant whose own reader docstring says print, table, published or reference value.
  - "Eq. (n)" needs that equation number written as a citation in the reader's file or brief.

  Tested: "Robertson printed reference value" on `rob_state40` now fails; before, any registered reading backed it.
- Pairs that `source_names_baseline.txt` already grandfathers pass. New pairs need the shrink-only
  `scripts/trust/source_variants_baseline.txt`.
- **V4 (`--base`).** That baseline may not grow, and the alias file may not lose or change a line.

### 5. `scripts/trust/check_prose_gen.py` (limit 6)
The new words are: throughout, at all times/points/instants, all the time, always, never, forever, for all time, at no
time, everywhere, anywhere, wherever, whenever, nowhere, for/over/on/across/along the whole/entire, the entire, all along,
from start to end, uniformly in time/t/space/x/z, permanently, at every/each/any instant/moment/time; and in general,
generally, globally, universally, invariably, without exception, unconditionally, in all/every case(s), regardless,
irrespective, independently, for each and every.
- **G1.** `check_prose.param_rule` runs with these words, which reports phrases naming a fixed parameter. Separately,
  a time/space word needs a universally bound variable of non-function type. "y₂ stays positive throughout" on
  `rob_state40` (which binds only the solutions y₁, y₂, y₃) fails, and so do "always", "never" and "for the whole".
- **G2.** A statement with no universal data may not use any of these words.
- **G3.** These words over data restricted by a pinned `Is…` predicate need that predicate's glossary term
  (rule 10).
- **G4 (`--base`).** `scripts/trust/prose_gen_baseline.txt` only shrinks.

## CI wiring (`.github/workflows/lean.yml`, blocking, same style; YAML parses)
- **Trust step**, after `check_templates.py`: `check_literal_targets.py`, `check_source_variants.py`,
  `check_prose_gen.py`.
- **Relock step**, after `check_blind_route.py --base "$BASE"`: `--base "$BASE"` forms of those three, plus
  `check_reader_frozen.py --base "$BASE"` and `check_brief_leak.py --base "$BASE"`.

## Registries and baselines created
| file | entries | kind |
|---|---|---|
| `scripts/trust/literal_slots.txt` | 5 (robK1→k₁, robK2→k₂, robK3→k₃, robInit→a₀ b₀ c₀, robT→T of IsRobSolution) | grows only with a LEDGER line |
| `scripts/trust/literal_target_baseline.txt` | 2 | shrink-only |
| `scripts/trust/source_aliases.txt` | 31 alias lines (20 existing keys + 11 new) | grow-only |
| `scripts/trust/source_variants_baseline.txt` | 0 | shrink-only |
| `scripts/trust/prose_gen_baseline.txt` | 7 | shrink-only |

The two `literal_target_baseline.txt` entries:
- `table5_oL_aicc_unattainable`: `21.41 0.005`. This is the printed Table 5 AICc plus half a digit on the "target" side.
  It is a genuine T1 case and was never read twice.
- `rob_state40`: six `40`s in `y₁ 40 … y₃ 40`. These are evaluation times that were covered by robT by value only.

The seven `prose_gen_baseline.txt` entries are the B1Fit and L19 headlines, each saying "on the whole interval back to
the farther source". The phrase describes the domain of a universally bound hypothesis, and the param-noun registry
reads "interval"/"source" as the fixed redshift roles. These are probably false positives, kept visible.

## Verification on the current tree (6fc653c + these files; `.lake/meaning.jsonl` of 2d83dad)
- **New checks.** All five pass:
  - the three non-base scripts plain;
  - every `--base` form against HEAD, 66604e8 (this run's start), 8a64b6d (this run's push base), `5fd0bce~1` and
    `cedc72c~1` (before the kappa and Robertson routes).
- **Existing checks.** Unchanged and still ok: check_prose, check_literals, check_source_names, check_templates,
  check_provenance, check_formulas, check_numbers.
- **Synthetic tests.**
  - Function-level: T1 grammar, slot coverage (`y₂ 40 < 40`, a run `1 0 0` outside the call, swapped k₁/k₂), V1–V3
    docstrings, G1/G2 docstrings.
  - Scratch git clone (`.../scratchpad/t`): the append attack (F1, F2) and the leaking brief (L1–L3).
- **Not mine, but it blocks the push.** The **existing** `check_blind_route.py --base 8a64b6d` FAILS on this run's own
  route. Its B3 rule finds the code line `import Mathlib.Data.Real.Basic` (25 or more characters) inside
  `brief_robL.md`, because the brief quotes the file template. This is a false positive of B3, and CI's relock step
  will be red when this run pushes. I did not change it, because the brief forbids weakening a check. Suggested fix:
  exempt `import` lines and `namespace`/`end` lines from the code-line test, disclosed in LEDGER.

## What remains uncheckable
- **Targets.** One printed number compared with a weak bound (`1 < 0.37464`) is still a one-number target. A `target`
  slot is compared by value only.
- **Slots.** The slot registration is the author's (disclosed in LEDGER), not the reader's.
- **Briefs.** These still pass:
  - formulas that compute the answer;
  - the answer named by reference or by a path to a file;
  - other languages, Roman numerals, unit conversions;
  - anything said to the reader outside the committed brief.

  L3 may give false positives on briefs with juxtaposed numbers ("2.4, 2008"). It fails closed.
- **Names.** These are not read:
  - a model or author missing from both registries;
  - non-Latin scripts.

  Backing shows that the reader or a reached transcription *names* the source, not that the source says what the
  docstring claims.
- **Generalisation.** These are not read:
  - generality without a listed word ("isochronous", "stays positive");
  - generality carried only by the headline's name.

  G1 cannot tell which bound variable a word ranges over: a statement binding `t` for one purpose and fixing time
  elsewhere passes.
- **Blindness.** Whether the reader was blind is still uncheckable within one push: brief, forged reading and copy in
  three commits.
- **Future promotion.** Promoting `rob_printed_y3_low` with `robY3Ref` will need a `robY3Ref target` line in
  literal_slots.txt, a LEDGER line, and a match of the value against the statement's `9999999791665050 / 10 ^ 16` term.
