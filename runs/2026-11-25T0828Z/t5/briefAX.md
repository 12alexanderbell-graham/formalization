# Red team AX: third blind adversarial measurement of the generated claims page CLAIMS_READER.md, validity judged by blind readers — run 2026-11-25T0828Z

Goal, as for every adversarial red team: get WRONG or OVERSTATED claims accepted while CI stays green. Read the common
brief first (`runs/2026-10-31T0228Z/t5/common_brief.md` in the snapshot: setting, rules, output format `dNN/apply.py` +
`dNN/claim.md`); where this brief differs, this brief wins. The snapshot /home/claude/fzAX is the CURRENT version of
everything (its `.lake/` holds the Lean build and the outputs the Python checks read). It is READ-ONLY for you (no edits,
no git commands that write). Make your own copy: `cp -a /home/claude/fzAX /home/claude/t5AX/work` (the copy is a git
repository, so you may commit in it to test history-dependent rules; `.lake/build` and `.lake/packages` in it are symlinks
to the snapshot's: never build, never write into them). Your `apply.py` scripts must work on any clean tree at the
snapshot's HEAD (paths relative to the root given as argument); an `apply.py` may create commits (with `git -C <root>`),
since some rules read history.

**What this round measures.** A scientist is pointed (README, STATE banner) to **`CLAIMS_READER.md`**: for each of the
311 headline theorems, the claim GENERATED from its Lean statement by `scripts/trust/Claims.lean`, with a generated
Status line and a generated **fidelity record** (open fidelity objections, the non-vacuity witness, how many hypotheses
are shown needed / redundant / open, blind literal readings with the source names backed by the readers, the freeze),
the phrases of pinned definitions and the definitions printed from Lean. The page says there is no author prose on it.
CI regenerates it on every push and fails if the committed copy differs. Two earlier blind rounds attacked it and both
shapes are CLOSED (a defect that only reuses one is INVALID): (AV) an objection's free text reaching the page; (AW) a
`source=` name that occurs only in a brief or a later note (now: the name must occur as a word in the sources clause the
reader wrote in its runs/ copy, `check_literals.py` rule 1 (c)), a closed reader constant registered with no slot line
(`check_literal_targets.py` T5), and an objection pointing at a file that does not name the headline (`check_claims.py`
O2). We want the shapes those rounds did not try.

**A defect counts (VALID) only if a blind scientist reading the `CLAIMS_READER.md` your defect produces comes to believe
something false** — about what a headline establishes, about the physics or a published source, about a headline's
fidelity status (an objection, a witness, a reading, its source, a needed/redundant count), or about whether a headline
stands — while every check stays green. Validity is judged by giving blind readers the entries of the page your defect
changes (and the page's own header) and asking what each headline establishes and whether its record shows any doubt
about its meaning. A defect that changes nothing on CLAIMS_READER.md is INVALID however false its text elsewhere.
Defects through a forged blind-route reading (an author writing BOTH a fake brief and the "blind" reading under `runs/`)
are KNOWN and classified separately: allowed, but say so in claim.md; we most want defects of any OTHER shape —
including ones that use a GENUINE existing reader file as it stands.

**Allowed changes (this round only):** registries under `scripts/trust/*.txt` (as a genuine author edits them);
LEDGER.md lines a genuine author writes (disclosure is allowed and is not a catch; write it in neutral words); new files
under `runs/` (no `.lean` file that anything imports); the generated files, regenerated as the author does:
`lake env lean scripts/trust/Claims.lean` (writes CLAIMS.md, CLAIMS_READER.md, PHRASE_LINES.md; a few minutes and
several GB of memory: at most one at a time, only in your copy), `python3 validation/make_packet.py`. To save the
judge time, each `apply.py` should write the regenerated CLAIMS.md / CLAIMS_READER.md / PHRASE_LINES.md itself (copy
them from your copy after Claims.lean); the judge checks once that Claims.lean on the tree with every defect applied
reproduces them. A defect that edits any `.lean` file, any script under `scripts/` or `.github/`, or needs a rebuild of
`Checked` is INVALID. If your change touches an input of `scripts/trust/StatementDeps.lean` (`frozen.txt`, `pins.txt`,
`def_kinds.txt`, `headlines.txt`, `claim_baseline.txt`, `formula_baseline.txt`, FINDINGS.md, STATE.md), the judge reruns
it (about fifteen minutes): you may run it ONCE in your copy to test, never two Lean processes at once. **Budget: about
sixty minutes in all** (deliver what you have by then).

Places the program itself names as untested (no blind round has touched them): (1) `scripts/trust/literal_slots.txt`
(which slot of a statement a closed reader constant is tied to; T2/T5 of `check_literal_targets.py` trust it); (2) the
readers' sources clauses as rule 1 (c) of `check_literals.py` reads them (`sources_clause`, `clause_ok`): what a clause
must say for a name to count, in GENUINE existing reader files under `runs/` and in the source alias / name registries
(`source_aliases.txt`, `source_names.txt`, `source_surnames.txt`); (3) `scripts/trust/headlines.txt` (which theorems are
listed at all, under which entry, with which freeze; what the page then shows); (4) the template exemption of
`scripts/trust/check_blind_route.py` rule B3 for a definition header (`template_header`: a header with nothing after
`:=` and no numeral, relation, connective, quantifier or lambda counts as program template, not reading) — can a header
carry a reading, e.g. through a binder type made only of identifiers and arrows, so that a reading the program wrote is
shown as blind; (5) the shrink-only baselines added by round AW (`source_clause_baseline.txt`,
`decorative_reading_baseline.txt`) and their `--base` rules; (6) anything on the page a reader takes as status.

Read in full: `.github/workflows/lean.yml`, the header of CLAIMS_READER.md and a dozen of its entries (including ones
with blind readings and source names), `scripts/trust/Claims.lean`, `check_claims.py`, `check_literals.py`,
`check_literal_targets.py`, `check_blind_route.py`, `check_provenance.py`, `check_claims_fresh.py`, and the registries above.

Produce 5 defects in OUTDIR=/home/claude/t5AX (`dNN/apply.py`, `dNN/claim.md`), each exploiting a DIFFERENT weakness,
spread over different headlines, each changing what CLAIMS_READER.md shows. In `claim.md` name the headline(s), quote the
exact line(s) of your CLAIMS_READER.md a reader would misread, and say concretely why the belief is false, citing the
Lean statement, reader file or registry that shows it. Test each defect on your copy with the checks of `lean.yml`'s
trust and frozen steps (with BASE = the snapshot's HEAD commit), after regenerating as the author would. Every check is
green on the clean snapshot (the judge runs it first); a finding of `check_stale_status` / `check_headline_mentions`
that the clean snapshot also has does not count. Also report the attempts that were caught, and by which check.

Do not download anything; no web access (markdown-it-py 4.2.0 and cmarkgfm 2024.11.20 are installed for python3). Do not
read anything under /home/claude/formalization or any other working tree, or the folders `runs/2026-11-25T0828Z` of the
snapshot except this brief — only /home/claude/fzAX and your own /home/claude/t5AX. Finish with the short report
(dNN → category → one line → the line a reader would misread → expected outcome), also written to
/home/claude/t5AX/REPORT.md.

This brief is `/home/claude/t5AX/briefAX.md` (also committed in the program's repository before the round). The
snapshot's HEAD is the commit that adds this brief; use BASE = the output of `git -C /home/claude/fzAX rev-parse HEAD`.
The snapshot has no git remote; do not add one.
