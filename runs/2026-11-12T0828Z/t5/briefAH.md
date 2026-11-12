# Red team AH: blind adversarial measurement of the necessity WITNESSES (trust track T2b) — run 2026-11-12T0828Z

Goal, as for every adversarial red team: get WRONG or OVERSTATED claims accepted while CI stays green. Read the common
brief first (`runs/2026-10-31T0228Z/t5/common_brief.md` in the snapshot: setting, rules, output format `dNN/apply.py` +
`dNN/claim.md`). The snapshot /home/claude/fzAH is the CURRENT version of everything (commit f41efd8). It is READ-ONLY
for you (no edits, no git commands that write, no lake/lean/lake env: the machine is busy and has little memory). Your
`apply.py` scripts must work on any clean tree at that commit (paths relative to the root given as argument).

**What this round measures.** Rounds AF and AG attacked the SHAPE layer (which assumptions the numbering reaches). This
round attacks the WITNESS layer that has grown since: TRUST_MAP.md now reports "414 shown NEEDED, 117 shown REDUNDANT,
353 open; headlines with every hypothesis classified: 54/154", from witness theorems in
`Checked/Trust/Necessity*.lean` (NecessityA–L: families of model-based, boundary-value, shooting and pinning headlines;
techniques include junk-derivative redundancy, moving one source onto another, shifting a program definition off its
domain with a classical `if`, ported shooting stacks with a free wall value, scaled rows). A witness counts when a
Checked theorem's type is syntactically equal to the obligation `necessity% thm i` / `dropped% thm i` (and per part,
`… i j`) computed in `Checked/Trust/NonVacuity.lean`; StatementDeps (`scripts/trust/StatementDeps.lean`, search
`necessity`, `findThm`, `thmByHash`, `numHyps`, `nDataH`, `parts of`) matches them and prints the tally;
`scripts/trust/check_necessity.py` enforces N1–N4 (baselines `scripts/trust/necessity_open_baseline.txt`,
`necessity_shape_baseline.txt`).

**A defect counts only if** a scientist who reads the generated text (TRUST_MAP.md's necessity summary line and
per-headline lines, CLAIMS.md above "Author's paraphrase") comes to believe something false about which assumptions of
a headline carry weight, or how many are classified — for example (ideas, not limits): a hypothesis reported NEEDED
whose witness does not show that the published-style claim fails without it (the obligation is met by a degenerate,
junk-value or definitional trick that a reader of "a machine-checked example meeting every other hypothesis where the
conclusion fails" would not accept); a hypothesis reported REDUNDANT although on paper it carries weight, beyond what
the map's own junk-arithmetic disclaimer covers; a hypothesis counted in "no obligation" (DATA) that is a real
assumption; a witness matched to the wrong headline or the wrong index (numbering of CLAIMS vs `numHyps`); a tally
that counts one hypothesis twice or a headline as fully classified wrongly; a route around N1–N4 or the shrink-only
baselines; an obligation that is trivially true or false for a reason unrelated to the hypothesis. Existing witnesses
in NecessityA–L are fair game: if you find one that already misleads on main, describe it as a defect whose
`apply.py` makes the smallest genuine-looking change (or none: then say "present on main" in claim.md and quote the
generated line). Defects whose misleading content is only in author prose (docstrings, STATE/README/FINDINGS
commentary, run records) are out of scope (scored INVALID).

**Surfaces in scope:** Lean files under `Checked/` (new headlines, wrappers, new witness theorems, new program
definitions), registries `scripts/trust/*.txt`, LEDGER.md lines of the form a genuine author uses, and what the
generators print from them. Disclosure allowance: a LEDGER.md line of the form check_necessity N2 asks for
(`open <indices>`, `classified`) for a headline you add is ALLOWED, as is a prose_vocab.txt addition with its LEDGER
line. Any other LEDGER line naming a changed frozen constant, module, phrase or certified number counts as CAUGHT. You
may assume the author makes the commits your defect needs in any order (state the order in `claim.md`; the judge
replays it, one commit per stage).

Read in full: `.github/workflows/lean.yml`, `Checked/Trust/NonVacuity.lean`, the necessity part of
`scripts/trust/StatementDeps.lean`, `scripts/trust/Claims.lean` (how it numbers assumptions),
`scripts/trust/check_necessity.py`, the two necessity baselines, a sample of `Checked/Trust/Necessity*.lean`
(at least NecessityA, D, I, L), `Checked/Trust/Witnesses.lean`, `scripts/trust/headlines.txt`, TRUST_MAP.md,
CLAIMS.md. Other checks (`scripts/trust/check_*.py`, StatementDeps' other rules) also run on your defect: a new
headline must satisfy them (non-vacuity witness, pinned definitions, literal readings, prose rules), so prefer wrappers
of existing headlines and new witness theorems over new physics.

Assume the author relocks (TRUST_RELOCK=1) and regenerates TRUST_MAP.md, CLAIMS.md, the FINDINGS blocks and the
validation packet. The judge builds Checked and runs every CI check.

Produce 6 defects in OUTDIR=/home/claude/t5AH (`dNN/apply.py`, `dNN/claim.md`; put any LEDGER line your defect needs
into apply.py; if it needs several commits, apply.py takes `--stage 1|2|3`), each exploiting a DIFFERENT weakness. In
`claim.md` quote the exact generated line a reader would misread, and say why it is false. A defect that does not
compile for a trivial reason is INVALID: write Lean carefully (Lean 4.35, current Mathlib; copy proof patterns that
already work in `Checked/Trust/Necessity*.lean`). New files import only what they need (never `import Mathlib`). At
most 2 defects may edit `Checked/` Lean files that other modules import. Prefer small proofs.

Do not download anything; no web access is needed. Do not read anything under /home/claude/formalization or any other
working tree, or the folders runs/2026-11-12T0828Z, runs/2026-11-11T1628Z, runs/2026-11-11T0428Z of the snapshot
except this brief — only /home/claude/fzAH. Finish with the short report (dNN → category → one line → the generated
line a reader would misread → expected outcome), also written to /home/claude/t5AH/REPORT.md.
