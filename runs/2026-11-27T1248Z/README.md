# Run 2026-11-27T1248Z (external test: target O correction, then the release index)

**THE RESULT:** part 3 (what the gates catch on AI-produced mathematics the program did not make): target O's coverage
step corrected and generalised. Families are now mapped through OpenAI's scope documents, and every gap is classed as
disclosed or undisclosed. Of the twelve gaps reported earlier, none is an undisclosed Lean mismatch, and one (O10) was
our own error, now withdrawn with a Lean closure. A new gate read all 246 Lean-linked items of the release index with
two readers each: **51 put the "[Lean]" link on a headline claim that no linked Lean statement states**, and their scope
text does not say so.

**What can a scientist now trust without checking it themselves, that they could not before?** For every one of the
246 Lean-linked items of OpenAI's 6 October release, which headline claims the Lean actually states and which it does
not. Each entry is two independent readings against the challenge files, with file and line
(`validation/EXTERNAL_O.md`, Index check). For O1–O37, which earlier "gaps" OpenAI itself disclosed. Also that the
explicit F of O10 is the F of the `CommutingDerivations` challenge, and that every reader's "F is not a coordinate"
follows from it (Lean, standard axioms locally; replay queued).

**Weakest unchecked step:** the index verdicts are readings, not Lean facts. Two model readers agree on each, but the
two readers are different models from one family, and no verdict is closed in Lean: each says only that a
statement is absent. Also, the replay of the O10 closure (`O-noncoord-cd`) has not run: GitHub's runner queue has been
saturated since 10:22Z.

## Start
- 12:48Z. The clone was detached at abfeba1. Local `main` was stale and unrelated after the force-update, so I worked on
  a local branch made from origin/main (a reset was refused by the environment's classifier).
- `LOCK` is held by run 2026-11-27T1228Z (part 1, started 12:28Z, alive), so `STATE.md` and the active proof files were
  not touched.
- `EXTERNAL_LOCK` was free and was taken at 5171889. The PROMPT's "Target O correction, at once" (12:46Z) was the first
  step.
- Env: repo ok (`add_repo` not exposed; clone present, push works). elan and the Mathlib cache installed. openai/math
  cloned at the pin 3344da5.

## Target O correction (`EXTERNAL_O.md` Correction 2)
- `formalization.yaml` has no paper ↔ challenge link at the pin: no `main_results` entry carries a paper id, and its
  `sources` list 186 papers.
- The map is the scope documents `lean/docs/NNN.md`: 248 documents, which link 424 of the 425 challenges. Tool:
  `scripts/external/family_map.py`.
- Gaps reclassified:
  - Disclosed: O7, O9, O14, O19, O22, O24, O31, O33.
  - Not gaps: O26, O36.
  - O1: disclosed in CONTENTS.
  - O3: Gottschalk is refuted in the family's Lean by `OddKaplansky`.
  - **O10: withdrawn.** `CommutingDerivations` names F. Closure `O/noncoord/Closure.lean`: 3/3 readings of "F is not a
    coordinate", compiled locally. Replay line `O-noncoord-cd`.
  - O21 has seven challenges (`GrahamSpherical` was missed).
- Referee (Sonnet, raw files only) confirmed the facts. Alexander messaged with the corrected list.

## Release index (`EXTERNAL_O.md` Index check)
- `family_map.py --contents` reported 70 items whose index entry names papers the document does not cover. 26 of them
  were flagged as leads, then all 246 items were read.
- Readers: first Sonnet (11 auditors in all), second Opus (4 auditors). Items 197, 084, 150, 095, 207, 143, 076, 271,
  251, 015, 058, 182, 184, 307 and 365 were also checked here against the challenge files.
- Results:
  - **51 overstatements.** Item 143 ("Resolves … Hilbert's sixteenth problem"; the Lean covers quintic Liénard only)
    is the most consequential.
  - 11 minor, 54 disclosed, 130 match.
  - 4 scope documents contradict their own links.
- Alexander messaged three times as the counts firmed up.

## Next
- CI: external replay runs 45981618513 … 46003398573 have been queued since 10:22Z (runner limit). Read them in order.
  `O-noncoord-cd` and `O-matroid` were dispatched in 46003398573.
- The 0628Z Next list still stands:
  - Target R leanchecker shards (run 45985482988), then the comparison with the published checks.
  - The open closures: O20 B/C, O21 A/C, O34 A/B, O36's ℝ⁹ transport, O37 Corollary 1.4, O31 B/C, O32 A, O26.
- Then target O families 38+: `family_map.py --challenge <Name>` first, then the brief. Then target M.
- Turn the index check into a standing gate for any outside release: each headline claim maps to a named Lean
  theorem or to an explicit "not formalized" line.
- After the index verdicts are committed (blind rule), read published reviews of the release and record what they
  found that the index check did not, and the reverse.
