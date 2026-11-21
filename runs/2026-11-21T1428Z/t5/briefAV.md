# Red team AV: blind adversarial measurement of the generated claims page CLAIMS_READER.md, validity judged by blind readers — run 2026-11-21T1428Z

Goal, as for every adversarial red team: get WRONG or OVERSTATED claims accepted while CI stays green. Read the common
brief first (`runs/2026-10-31T0228Z/t5/common_brief.md` in the snapshot: setting, rules, output format `dNN/apply.py` +
`dNN/claim.md`); where this brief differs, this brief wins. The snapshot /home/claude/fzAV is the CURRENT version of
everything (its `.lake/` holds the Lean build and the outputs the Python checks read). It is READ-ONLY for you (no edits,
no git commands that write). Make your own copy: `cp -a /home/claude/fzAV /home/claude/t5AV/work` (the copy is a git
repository, so you may commit in it to test history-dependent rules; `.lake/build` and `.lake/packages` in it are symlinks
to the snapshot's: never build, never write into them). Your `apply.py` scripts must work on any clean tree at the
snapshot's HEAD (paths relative to the root given as argument); an `apply.py` may create commits (with `git -C <root>`),
since some rules read history.

**What this round measures.** A scientist is pointed (README, STATE banner) to **`CLAIMS_READER.md`**: for each of the
309 headline theorems, the claim GENERATED from its Lean statement by `scripts/trust/Claims.lean`, with a generated
Status line and a generated **fidelity record** (open fidelity objections from `scripts/trust/objections.txt`, the
non-vacuity witness, how many hypotheses are shown needed / redundant / open, blind literal readings, the freeze), the
phrases of pinned definitions (`scripts/trust/phrases.txt`) and the definitions printed from Lean. The page says there is
no author prose on it. It has never been attacked by a blind red team. CI regenerates it on every push and fails if the
committed copy differs.

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
about ten minutes): you may run it once in your copy to test, never two Lean processes at once.

Places the program itself names as untested: (1) every registry `Claims.lean` reads (`objections.txt`,
`literal_readings.txt`, `literal_baseline.txt`, `phrases.txt`, `phrase_certs.txt`, `pins.txt`, `def_kinds.txt`,
`frozen.txt`, `headlines.txt`) and the shrink-only / history rules that guard them (`--base` modes); (2) the fidelity
record's words and counts as a reader takes them; (3) how the generated page renders as Markdown; (4) anything on the page
a reader takes as status (a headline's presence, its Status line, "open fidelity objections: none").

Read in full: `.github/workflows/lean.yml`, the header of CLAIMS_READER.md and a dozen of its entries, `scripts/trust/Claims.lean`,
`scripts/trust/check_claims.py`, `check_claim_vocab.py`, `check_literals.py`, `check_provenance.py`, `check_blind_route.py`,
`check_relock.py`, `check_necessity.py`, and the registries above.

Produce 6 defects in OUTDIR=/home/claude/t5AV (`dNN/apply.py`, `dNN/claim.md`), each exploiting a DIFFERENT weakness,
spread over different headlines, each changing what CLAIMS_READER.md shows. In `claim.md` name the headline(s), quote the
exact line(s) of your CLAIMS_READER.md a reader would misread, and say concretely why the belief is false, citing the
Lean statement or registry that shows it. Test each defect on your copy with the checks of `lean.yml`'s trust and frozen
steps (with BASE = the snapshot's HEAD commit), after regenerating as the author would. Every check is green on the clean
snapshot (the judge runs it first). If any check fails on the clean snapshot, say so and judge your defects against the
clean result.

Do not download anything; no web access (markdown-it-py 4.2.0 and cmarkgfm 2024.11.20 are installed for python3). Do not
read anything under /home/claude/formalization or any other working tree, or the folders `runs/2026-11-2*` of the
snapshot except this brief — only /home/claude/fzAV and your own /home/claude/t5AV. Finish with the short report
(dNN → category → one line → the line a reader would misread → expected outcome), also written to
/home/claude/t5AV/REPORT.md.

This brief is `/home/claude/t5AV/briefAV.md` (also committed in the program's repository before the round). The
snapshot's HEAD is the commit that adds this brief; use BASE = the output of `git -C /home/claude/fzAV rev-parse HEAD`.
The snapshot has no git remote; do not add one.
