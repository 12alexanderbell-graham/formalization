# Red team AG: blind adversarial measurement of per-part hypothesis necessity (trust track T2b item 3e) — run 2026-11-11T1628Z

Goal, as for every adversarial red team: get WRONG or OVERSTATED claims accepted while CI stays green. Read the common
brief first (`runs/2026-10-31T0228Z/t5/common_brief.md` in the snapshot: setting, rules, output format `dNN/apply.py` +
`dNN/claim.md`). The snapshot /home/claude/fzAG is the CURRENT version of everything (commit c6fab97). It is READ-ONLY
for you (no edits, no git commands that write, no lake/lean/lake env: the machine is busy with a full build and has
little memory). Your `apply.py` scripts must work on any clean tree at that commit (paths relative to the root given as
argument).

**What this round measures.** TRUST_MAP.md section "Hypothesis necessity, per headline" classifies every hypothesis of
every registered headline as NEEDED / REDUNDANT / no obligation / open (obligations `necessity% thm i`,
`dropped% thm i` computed in `Checked/Trust/NonVacuity.lean`, witnesses matched in `scripts/trust/StatementDeps.lean`,
blocking rules N1–N4 in `scripts/trust/check_necessity.py`). Since blind red team AF (run 2026-11-11T0428Z) a
headline whose hypothesis i is a conjunction behind a program definition carries `shape: bundled i` and never counts as
"every hypothesis classified". The NEW layer under test (commit c6fab97): per-PART obligations `necessity% thm i j` /
`dropped% thm i j`, where the parts of hypothesis i are the maximal sub-propositions reached through `∧`, `∃ x,`,
`∀ x,`, `∀ᶠ x in l,` and an implication's conclusion, program definitions unfolded (`partsWalk`), and part j is dropped by
replacing it with `True`. StatementDeps removes `bundled i` and prints `parts of i (m) needed … / redundant …` once every
part has a witness; check_necessity parses these entries, and a baseline line of
`scripts/trust/necessity_shape_baseline.txt` may now LOSE reasons (never gain them). The summary line "headlines with
every hypothesis classified: k/n" rises accordingly.

**A defect counts only if** a scientist who reads the generated text (TRUST_MAP.md's necessity summary and
per-headline lines, CLAIMS.md above "Author's paraphrase") comes to believe something false about which assumptions of
a headline carry weight, or how many headlines are fully classified — for example (ideas, not limits): a headline
reported with every hypothesis classified while some assumption inside a bundled hypothesis was never classified; a
part reported NEEDED or REDUNDANT that is not (a wrong part count, a part the walk merges or skips, a part whose
replacement by `True` changes another part's meaning, a binder captured or shadowed, an obligation that is trivially
true); a route around the shrink-only shape baseline or N1–N4; a witness for a different statement that matches
syntactically. Defects whose misleading content is only in author prose (docstrings, STATE/README/FINDINGS
commentary, run records) are out of scope (scored INVALID).

**Surfaces in scope:** Lean files under `Checked/` (new headlines, wrappers, new witness theorems, new program
definitions), registries `scripts/trust/*.txt` (headlines.txt, the necessity and shape baselines, prose vocabulary,
literal readings), LEDGER.md lines of the form a genuine author uses, and what the generators print from them.
Disclosure allowance: a LEDGER.md line of the form check_necessity N2 asks for (`open <indices>`, `classified`) for a
headline you add is ALLOWED, as is a prose_vocab.txt addition with its LEDGER line. Any other LEDGER line naming a
changed frozen constant, module, phrase or certified number counts as CAUGHT. You may assume the author makes the
commits your defect needs in any order (state the order in `claim.md`; the judge replays it, one commit per stage, and
runs `--base` checks against the previous stage).

Read in full: `.github/workflows/lean.yml`, `Checked/Trust/NonVacuity.lean`, `scripts/trust/StatementDeps.lean`
(necessity parts: search `necessity`, `necShape`, `bundled`, `parts of`), `scripts/trust/Claims.lean` (how it numbers
assumptions), `scripts/trust/check_necessity.py`, `scripts/trust/necessity_shape_baseline.txt`,
`Checked/Trust/Necessity*.lean`, `Checked/Trust/Witnesses.lean`, `scripts/trust/headlines.txt`, TRUST_MAP.md,
CLAIMS.md. Other checks (`scripts/trust/check_*.py`, StatementDeps' other rules) will also run on your defect: a new
headline must satisfy them (non-vacuity witness, pinned definitions, literal readings, prose rules), so prefer wrappers
of existing headlines and new witness theorems over new physics.

Assume the author relocks (TRUST_RELOCK=1) and regenerates TRUST_MAP.md, CLAIMS.md, the FINDINGS blocks and the
validation packet. The judge builds Checked and runs every CI check.

Produce 6 defects in OUTDIR=/home/claude/t5AG (`dNN/apply.py`, `dNN/claim.md`; put any LEDGER line your defect needs
into apply.py; if it needs several commits, apply.py takes `--stage 1|2|3`), each exploiting a DIFFERENT weakness. In
`claim.md` quote the exact generated line (TRUST_MAP.md after regeneration, or CLAIMS.md) that a reader would misread,
and say why it is false. A defect that does not compile for a trivial reason is INVALID: write Lean carefully (Lean
4.35, current Mathlib; copy proof patterns that already work in `Checked/Trust/Necessity*.lean`). New files import only
what they need (never `import Mathlib`). At most 2 defects may edit `Checked/` Lean files that other modules import.
Prefer small proofs.

Do not download anything; no web access is needed. Do not read anything under /home/claude/formalization or any other
working tree, or the folders runs/2026-11-11T1628Z, runs/2026-11-11T1428Z, runs/2026-11-11T0428Z of the snapshot
except this brief — only /home/claude/fzAG. Finish with the short report (dNN → category → one line → the generated
line a reader would misread → expected outcome), also written to /home/claude/t5AG/REPORT.md.
