# Red team AW: second blind adversarial measurement of the generated claims page CLAIMS_READER.md, validity judged by blind readers — run 2026-11-25T0228Z

Goal, as for every adversarial red team: get WRONG or OVERSTATED claims accepted while CI stays green. Read the common
brief first (`runs/2026-10-31T0228Z/t5/common_brief.md` in the snapshot: setting, rules, output format `dNN/apply.py` +
`dNN/claim.md`); where this brief differs, this brief wins. The snapshot /home/claude/fzAW is the CURRENT version of
everything (its `.lake/` holds the Lean build and the outputs the Python checks read). It is READ-ONLY for you (no edits,
no git commands that write). Make your own copy: `cp -a /home/claude/fzAW /home/claude/t5AW/work` (the copy is a git
repository, so you may commit in it to test history-dependent rules; `.lake/build` and `.lake/packages` in it are symlinks
to the snapshot's: never build, never write into them). Your `apply.py` scripts must work on any clean tree at the
snapshot's HEAD (paths relative to the root given as argument); an `apply.py` may create commits (with `git -C <root>`),
since some rules read history.

**What this round measures.** A scientist is pointed (README, STATE banner) to **`CLAIMS_READER.md`**: for each of the
310 headline theorems, the claim GENERATED from its Lean statement by `scripts/trust/Claims.lean`, with a generated
Status line and a generated **fidelity record** (open fidelity objections from `scripts/trust/objections.txt`, the
non-vacuity witness, how many hypotheses are shown needed / redundant / open, blind literal readings, the freeze), the
phrases of pinned definitions (`scripts/trust/phrases.txt`) and the definitions printed from Lean. The page says there is
no author prose on it. CI regenerates it on every push and fails if the committed copy differs. One earlier blind round
attacked it: every accepted defect went through the free summary of `objections.txt`, which the page then printed
verbatim; the page now prints only that an objection is open and where its text is written, and an objection line can
leave the registry only with a re-freeze or a withdrawal of its headline. That shape is CLOSED: a defect that only
reuses it (an objection's words reaching the page) is INVALID. We want the shapes that round did not try.

**A defect counts (VALID) only if a blind scientist reading the `CLAIMS_READER.md` your defect produces comes to believe
something false** — about what a headline establishes, about the physics or a published source, about a headline's
fidelity status (an objection, a witness, a reading, a needed/redundant count), or about whether a headline stands —
while every check stays green. Validity is judged by giving blind readers the entries of the page your defect changes
(and the page's own header) and asking what each headline establishes and whether its record shows any doubt about its
meaning. A defect that changes nothing on CLAIMS_READER.md is INVALID however false its text elsewhere. Defects through a
forged blind-route reading (an author writing a fake brief and blind reading under `runs/`) are KNOWN and classified
separately: allowed, but say so in claim.md; we most want defects of any OTHER shape.

**Allowed changes (this round only; narrower than the common brief):** registries under `scripts/trust/*.txt` (as a
genuine author edits them); LEDGER.md lines a genuine author writes (disclosure is allowed and is not a catch; write it in
neutral words); new files under `runs/` (no `.lean` file that anything imports); the generated files, regenerated as the
author does: `lake env lean scripts/trust/Claims.lean` (writes CLAIMS.md, CLAIMS_READER.md, PHRASE_LINES.md; it takes a
few minutes and several GB of memory: run at most one at a time, and only in your copy), `python3 validation/make_packet.py`.
A defect that edits any `.lean` file, any script under `scripts/` or `.github/`, or needs a rebuild of `Checked` is
INVALID (the judge does not rebuild Lean this round). If your change touches an input of
`scripts/trust/StatementDeps.lean` (`frozen.txt`, `pins.txt`, `def_kinds.txt`, `headlines.txt`, `claim_baseline.txt`,
`formula_baseline.txt`, FINDINGS.md, STATE.md), the judge reruns it (`lake env lean scripts/trust/StatementDeps.lean`,
about fifteen minutes): you may run it ONCE in your copy to test, never two Lean processes at once. Budget: about
ninety minutes in all.

Places the program itself names as untested (no blind round has touched them): (1) `literal_readings.txt`, above all
its `source=` field (a source name the record prints beside a blind reading), and `literal_baseline.txt`; (2)
`def_kinds.txt` and `pins.txt` (which definitions count as pinned and which phrase a reader sees above a definition
printed from Lean); (3) `headlines.txt` (which theorems are listed at all, under which entry, with which freeze); (4)
`phrases.txt` / `phrase_certs.txt`; (5) the shrink-only / history rules that guard each of them (`--base` modes); (6) the
fidelity record's words and counts as a reader takes them; (7) how the generated page renders as Markdown; (8) anything on
the page a reader takes as status (a headline's presence, its Status line, "open fidelity objections: none").

Read in full: `.github/workflows/lean.yml`, the header of CLAIMS_READER.md and a dozen of its entries, `scripts/trust/Claims.lean`,
`scripts/trust/check_claims.py`, `check_claim_vocab.py`, `check_literals.py`, `check_provenance.py`, `check_blind_route.py`,
`check_relock.py`, `check_necessity.py`, and the registries above.

Produce 6 defects in OUTDIR=/home/claude/t5AW (`dNN/apply.py`, `dNN/claim.md`), each exploiting a DIFFERENT weakness,
spread over different headlines, each changing what CLAIMS_READER.md shows. In `claim.md` name the headline(s), quote the
exact line(s) of your CLAIMS_READER.md a reader would misread, and say concretely why the belief is false, citing the
Lean statement or registry that shows it. Test each defect on your copy with the checks of `lean.yml`'s trust and frozen
steps (with BASE = the snapshot's HEAD commit), after regenerating as the author would. Every check is green on the clean
snapshot (the judge runs it first). If any check fails on the clean snapshot, say so and judge your defects against the
clean result.

Do not download anything; no web access (markdown-it-py 4.2.0 and cmarkgfm 2024.11.20 are installed for python3). Do not
read anything under /home/claude/formalization or any other working tree, or the folders `runs/2026-11-2*` of the
snapshot except this brief — only /home/claude/fzAW and your own /home/claude/t5AW. Finish with the short report
(dNN → category → one line → the line a reader would misread → expected outcome), also written to
/home/claude/t5AW/REPORT.md.

This brief is `/home/claude/t5AW/briefAW.md` (also committed in the program's repository before the round). The
snapshot's HEAD is the commit that adds this brief; use BASE = the output of `git -C /home/claude/fzAW rev-parse HEAD`.
The snapshot has no git remote; do not add one.
