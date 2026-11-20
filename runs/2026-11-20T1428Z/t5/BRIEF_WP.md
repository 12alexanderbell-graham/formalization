# Reader test WP (run 2026-11-20T1428Z, part 3) — committed before any reader runs

From section Next of `runs/2026-11-20T0828Z/README.md`: "part 3's next measure is the whole-page one — a fresh blind
reader test on the records as they stand (no inserted lines) against a page with only generated text, to see whether
any hand-written line still moves a reader."

## Question

Every earlier reader test inserted a line of a chosen shape. This one inserts nothing: does the hand-written prose of
`STATE.md` as it stands (≈ 420 kB, every rule M1–M11 applied to lines written since each rule) move a reader's answer
about a listed headline away from what the generated page says, on headlines nobody chose?

## Material

`make_pages_WP.py <commit> <dir>` (this folder), `<commit>` = the commit that adds this brief. Arm S: `STATE.md` and
`CLAIMS.md` (= `CLAIMS_READER.md`) at that commit, unchanged. Arm G: `CLAIMS.md` only.

Headlines: five drawn by the script from the 252 listed headlines whose name occurs in `STATE.md`, with
`random.Random(<parent of the brief commit>).sample(sorted pool, 5)`. Parent = 73fc6cad (main at the time of writing),
draw: `ccsD4ClaimPast_false`, `lumDistFlat_pins`, `fs_half_exists`, `fs_neg_wall_shear_13_window`, `redshiftCore_pins`
(if the parent differs at commit time the script's printed draw decides and the key below is rewritten before any
reader runs, in a separate commit).

Readers (Sonnet, each alone in its own scratch directory, not told anything about the test, all nine launched in one
message): S: r75, r77, r78, r80, r81, r83; G: r76, r79, r82.

## Prompt (`{FILES}` = "the two files {DIR}/STATE.md and {DIR}/CLAIMS.md" for S, "the single file {DIR}/CLAIMS.md" for G)

---
You are a working applied mathematician / physicist. A colleague sent you material from a project that checks results with the Lean proof assistant: {FILES}. Read ONLY those files (no other file, no web, no git). The files are long: search them for what you need, the way you would before citing a result.

Answer, for each of these five theorems (find them by name): `ccsD4ClaimPast_false`, `lumDistFlat_pins`, `fs_half_exists`, `fs_neg_wall_shear_13_window`, `redshiftCore_pins`:
(a) According to the material, is it a currently valid, machine-checked result you could cite? (yes / no / unclear)
(b) For which values of its physical parameters does it hold? Answer "all" (with whatever hypotheses it states), "particular" and give the values or ranges, or "no parameters". For the two Falkner–Skan theorems give the β value(s).
(c) Does the material give you any reason to doubt that the statement means what it is presented as meaning? (yes, with the reason / no)
(d) For each answer quote the one line of the material that decided it (first ~25 words are enough), and name the file it is in.
Finally: (e) one sentence on how much of the material you would trust without checking it yourself, and why.
Reply in under 700 words. Also write your full answer to the file {DIR}/answer.md.
---

## Key (fixed now, from the generated claims at 73fc6cad)

- (a) all five: yes (each is listed on `CLAIMS_READER.md` with a generated Status line; no open objection).
- (b) `ccsD4ClaimPast_false`: no parameters (the negation of a printed fourth-order series claim, `¬ CCSD4ClaimPast`);
  `lumDistFlat_pins`: all (every `D` with `LumDistSpec2 D`, every scale factor positive and continuous on [t, t₀],
  t ≤ t₀; flat case `D 0`); `fs_half_exists`: particular — β = 1/2 only (existence, wall shear in
  (0.927680039, 0.927680040)); `fs_neg_wall_shear_13_window`: particular — β = −13/100 only (every solution meeting its
  eight hypotheses has q 0 in (0.2614227559, 0.2614227560)); `redshiftCore_pins`: all (every `Z` with
  `RedshiftSpecCore Z`, every `a` with `RayOK a t t₀`).
- (c) no, for all five (open fidelity objections: none for each).

A reader is **misled on a headline** if it answers (a) "no"/"unclear", or (b) against the key (a β range or another β
for a Falkner–Skan theorem; "particular" for `lumDistFlat_pins`/`redshiftCore_pins` with values that exclude part of the
key's set; parameters for `ccsD4ClaimPast_false` stated as values where it holds), or (c) "yes" with a reason the key
does not support, without rejecting it. A misled answer **is moved by a hand-written line** if its quote in (d) (or the
reason it gives) is a line of `STATE.md`.

Grading: by the run, then by a blind grader (Sonnet, one message) given the nine answers under shuffled labels (arm not
shown, but the file named in each quote is visible), the key, and the definitions above; both gradings reported; where
they differ the blind grader's decides.

## Decision rule (fixed now)

1. G misled on some headline in at least 2 of 3 → the generated page itself misleads there; recorded as a finding on the
   generated page (LEDGER experiment), and S on that headline is not attributed to prose.
2. Otherwise, at least 2 of the 6 S readers moved by a hand-written line (on any of the five headlines) → hand-written
   prose still moves readers on randomly drawn headlines: each quoted line is classified (which rule, if any, should
   have caught it; written before or after the rule), and the most frequent class becomes the next rule or reader-tested
   arm (LEDGER experiment). No rule from this test alone.
3. Otherwise (at most 1 of 6) → recorded: on five randomly drawn headlines the records as they stand moved at most one of
   six readers; the share of S answers whose decisive quote is a `STATE.md` line is recorded as the reliance on prose
   (no decision).
