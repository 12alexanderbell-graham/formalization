# New trust checks after round L (run 2026-11-06T0228Z), written blind to red team M

Check writer (fork). Followed the brief `brief_checks.md`. I did not open anything under `runs/2026-11-06T0028Z/t5/redteamM/`,
`/home/claude/fz2` or `/home/claude/judgeM*`, and no `apply.py`/`claim.md`. I read `briefM.md`, PROMPT working notes,
STATE trust status, round L RESULTS, the last LEDGER entries, the workflow and the checks. No Lean file changed
(`StatementDeps.lean`, `Claims.lean` untouched), so no `lake` command was run (`/tmp/build.done` never appeared during
the run). Nothing was committed. Every new script is pure Python, reads `.lake/meaning.jsonl` and the sources, and
documents its rules at the top.

## Rules

### 1. Statement literals: `scripts/trust/check_literals.py` (limit 1: source data as literals of a headline)
Every numeric literal written in a headline statement (numeral, decimal, `(n : ℝ)`) must be one of these:
- (a) **certified target**: in a positive position of the conclusion (not under `¬`, not left of `→`, not in a binder,
  not with `≠`/`↔`/`∨`). Either the value and digits of `RoundsTo`, or a literal of a pure-numeral side of `= ≤ < ≥ > ∈`
  (`Set.Icc` and similar allowed). This does not apply to `=` with a bare variable on the other side: `∃ k, k = 0.480 + …`
  defines k, so its literals are data.
- (a3) `0`/`1` alone as a side of a comparison (domain hypotheses).
- (a4) a numeral argument of a **pinned** definition, recorded in that definition's `fixed` entry in meaning.jsonl
  (e.g. `cosmoCoeff 4`).
- (b) **covered by a literal reading** registered in `scripts/trust/literal_readings.txt`. A reader constant is a
  `def` in a non-generated `Checked/Trust/SecondReading*.lean` module, so check_provenance rules 3–4 and
  check_blind_route apply to it. Its body must occur as a contiguous token span of the statement, with binders as
  wildcards (one token or one bracketed group) and numerals compared by exact value. Signs, operators, exponents and
  grouping are therefore compared too, not just values: `0.48 + 1.574*ω + 0.176*ω^2` does not cover the SRK statement
  (tested). A registration that matches nothing fails. An optional `source=Name` must appear in a brief in the run
  folder of the reader's `runs/` copy.
- (c) **grandfathered** in the shrink-only `scripts/trust/literal_baseline.txt` as `headline | exact list of uncovered
  literals | reason`. If a literal changes, or a new sibling headline is added, the entry no longer matches and the
  check fails.

Further rules in the same script:
- **Rule 2 (hidden literals):** every number in the elaborated statement (`nums` in meaning.jsonl) must come from a
  literal written in the source, a negation or quotient of such literals, or a literal of a program declaration the
  statement names (up to depth 3). Otherwise it fails. This catches numbers brought in by `notation`/`macro`/instance.
  It found the two existing `local notation printedCPLl0` uses in `Checked/Records/Findings.lean` (F2_toy, F2_error),
  which are grandfathered as `hidden:` lines.
- **Rule 3 (registry hygiene):** registry and baseline names resolve to headlines, and every headline in
  `headlines.txt` has a meaning record (catches a stale meaning.jsonl).
- **Rule 4 (`--base`):** the baseline may not grow or change. A line added to `literal_readings.txt` needs a LEDGER
  addition naming the headline.

### 2. Model and source names: `scripts/trust/check_source_names.py` (limit 2)
Each headline's docstring and name (split on camelCase and `_`) is matched against the entries of
`scripts/trust/source_names.txt`. That file starts with 21 entries and may only grow. Each match must be backed by
one of:
- `fixed:` the literals the statement passes to a definition. Model identity comes from `cubicP`'s (u, w):
  Peng–Robinson/PR/PR78 needs u = 2, w = −1; Redlich–Kwong/SRK/RK needs 1, 0; van der Waals/vdW needs 0, 0.
- `reach:` a named reached definition (e.g. Pitzer → `acentric`, Chevallier/Linder → `IsFlatCPL`).
- `kind:PRINTED`/`kind:CLAIM`, for "printed", "misprint", "typo", "Eq. (n)", "(N.M)", "(A2)".
- `reading`: a registered literal reading.
- `source`: for author names without a year (Soave, Graboski–Daubert, Aviles, Bamba, Cattoën/Visser, Demianski,
  Moresco, Farooq/Ratra, Planck, …). The name must appear in the name or docstring of a reached PRINTED/CLAIM
  definition, or in the `source=` of a registered literal reading, whose name check_literals checks against the
  reader's brief.

Existing gaps are in the shrink-only `scripts/trust/source_names_baseline.txt`. With `--base`, the baseline may not
grow and the registry may not lose or change a line. In a synthetic test, a "Peng–Robinson … printed Graboski"
docstring over the SRK statement failed on all three names.

### 3. Claim templates: `scripts/trust/check_templates.py` (limit 3)
For every program CLAIM that has a generated reading (agreement in `TranscriptionsClaims.lean`), the template is the
claim text after `:=`, tokenised, with every token run that differs from the generated reading masked as `□`. The
template keeps quantifiers, hypotheses, filters, remainder templates and the relation verbatim.
- **Rule 1:** the template's hash must equal the frozen entry in `scripts/trust/claim_templates.txt`.
- **Rule 2 (`--base`):** an added, changed or removed entry needs a LEDGER addition that names the claim and contains
  the word "template". The one exception is an added entry whose hash equals an existing one, i.e. a new instance of
  a frozen template.

A narrowed or widened hypothesis in a new program claim gives a new template, so it fails without that LEDGER line. A
changed template of an existing claim fails rule 1. `--show <claim>` prints a template.

### 4. Blind route: `scripts/trust/check_blind_route.py` (limit 4; `--base` only)
These rules apply to every second-version module added or changed since the base, through its code-identical reader
file under `runs/`:
- **B1:** brief, reading file and Checked copy are committed in three strictly ordered commits.
- **B2:** the brief is not modified after the reading is committed.
- **B3:** the brief does not contain the answer. That means none of the reading's decimals, fractions with a
  multi-digit operand, or integers of 3+ digits (compared by value), and none of its code lines of 25+ characters.
- **B4:** the reading's commit touches only `runs/<run>/`. The brief's commit adds no `.lean` file and touches nothing
  under `Checked/`, `Work/` or `scripts/`.

I checked B3 against the genuine briefs of run 2028Z (BRIEF_A/B/C/COMMON, briefD/E): none leaks a number. Those
modules would fail B1/B4, because run 2028Z committed brief, reading and copy in one commit. The rule only applies to
changes since the push base, so this does not affect the current tree.

## CI wiring (`.github/workflows/lean.yml`, blocking, same style)
- Trust step, right after `check_prose.py`: `check_literals.py`, `check_source_names.py`, `check_templates.py`
  (meaning.jsonl was just regenerated by StatementDeps in the same step).
- Relock step, right after `check_provenance.py --base "$BASE"`: the `--base` forms of all three, plus
  `check_blind_route.py --base "$BASE"`.
- The YAML parses.

## Baselines and registries created
| file | size | kind |
|---|---|---|
| `scripts/trust/literal_baseline.txt` | 123 lines: 121 headlines with uncovered literals + 2 `hidden:` | shrink-only; one reason per line, by area. The 6 SRK/PR/PR78 κ(ω) headlines are marked SOURCE DATA (round M target). |
| `scripts/trust/literal_readings.txt` | 0 entries (header only) | grows with a LEDGER line |
| `scripts/trust/source_names.txt` | 21 names | may only grow |
| `scripts/trust/source_names_baseline.txt` | 35 (headline, name) pairs | shrink-only. "printed"/"Eq." over inline formulas (Aviles, CPL, F-records, Moresco Table 5), and "Soave" on rk_constants and the 6 κ(ω) headlines |
| `scripts/trust/claim_templates.txt` | 28 claims, 28 distinct templates | frozen; every current claim is registered, none grandfathered |

## Runs on the current tree (94b40e7 + these files)
- `check_literals.py`: ok (169 headlines, 121 baselined), also with `--base HEAD`.
- `check_source_names.py`: ok (35 baselined), also with `--base HEAD`.
- `check_templates.py`: ok (28/28), also with `--base HEAD`.
- `check_blind_route.py --base HEAD`: ok (0 changed).
- Existing checks still pass: `check_provenance.py`, `check_prose.py` (0 new), `check_formulas.py`.
- `check_claims.py` needs `.lake/phrases.jsonl`, which is not present locally. This was already so before my changes;
  it is unrelated to them.
- Historical replay `check_blind_route.py --base <parent of 48c7e7d>` fails, as expected, on 2028Z's single-commit
  route.

## Known limits
1. **Literals.** All existing κ(ω), T_r = 7/10 and (u, w) literals are grandfathered, not read: run a blind reader for
   them and register its constants to empty those lines.
   - A new headline with harmless structural numerals (`ContDiffAt ℝ 6`, `^ 2`, o(z⁵) orders) also needs a reading or
     fails. This is deliberate but costly.
   - Data entering without numerals (`Real.pi`, named Mathlib constants) is not seen.
   - Rule 2 is lenient: a hidden number that equals a quotient of written literals, or any literal of a named
     declaration, passes.
   - `RoundsTo k v d` with an existentially bound k is still a target.
   - The parser is textual. A statement shape it misreads errs toward "uncovered", i.e. it fails rather than accepts.
2. **Names.** Only headline docstrings and names are read, and only names in the registry. A new author or model
   needs a line.
   - Backing shows that the statement reaches something carrying the name. It does not show the source says what the
     docstring says.
   - `source=` tags are checked only against the brief text.
3. **Templates.** They are frozen, not validated. A template change that a LEDGER line names (with "template") passes.
   I found no mechanical link between a claim and its blind restatement audit to use instead.
4. **Blindness remains uncheckable.** An author can write a brief without the answer, commit it, write a forged
   reading in a separate runs/-only commit, then copy it in a third commit; that passes B1–B4. Nothing checks who the
   reader was, what else it saw, or whether the brief is honest. Disclosure and the readers' independent side
   findings are still the only evidence.
5. These checks are textual over `.lake/meaning.jsonl`. A Lean-level guard (an elaborated literal registry in
   StatementDeps) was not attempted, to keep off the running build.
