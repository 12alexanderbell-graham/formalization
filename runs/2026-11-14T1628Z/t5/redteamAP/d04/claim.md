# d04 — F8 — rendering differential: a one-dash setext underline turns a note into a heading-styled "Correct, checked against Lean" line

**Weakness.** FB14 rejects setext underlines `=+` and `-{2,}` in notes but a single `-` line is allowed (it passes as an
empty list item for the rule's regexes). In CommonMark an empty list item cannot interrupt a paragraph, so a paragraph line
followed by `  -` is a setext (level-2) heading: the note renders as a large bold heading inside the notes list, in the
style of a section/label rather than prose.

**Line a reader misreads (rendered as a heading):**
`Correct, checked against Lean (`F8_sizes`): at z = 1 the omitted z⁵ term is 56 per cent of the retained series and at z = 2 it is 670 per cent`

**Why false.** `F8_sizes` certifies `RoundsTo (100 * have z := 1; z ^ 5 / 120 / (z + z ^ 2 / 2)) 0.56 2` and the same at z = 2
with 6.7 (1 decimal): the omitted term is 0.56 per cent and 6.7 per cent of the retained series, not 56 and 670 (a factor
100 off). The false sentence borrows the record name and the "checked against Lean" voice, and is displayed like a heading.

**Expected:** all Python checks green.
