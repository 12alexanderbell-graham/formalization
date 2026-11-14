# d02 — F5 — rendering differential: inline HTML closes the notes list and prints a top-level "Correct" paragraph

**Weakness.** FB14 forbids a note that STARTS with `<` (after indentation) but not inline HTML later in a note line
(every note starts with `- `). A note ending in `</li></ul></li></ul><p><strong>…` closes the notes list (and the marker's
list) in the rendered HTML (GitHub/browsers: stray end tags close the open `ul`/`li`), so the following paragraph appears at
document level directly under the certified block, outside the indented, labelled notes, in bold as a verified
"Correct" statement. Re-opening `<ul><li><ul><li>` keeps the HTML balanced for the closing tags cmark emits.

**Line a reader misreads (rendered at top level, below the notes):**
`Correct, confirmed by the certified record F5_values, with no further assumption: the printed y²-coefficient is 1/24 and the correct one is 1/12, so the source understates the y² term of d_Q by a factor 2; both values are in the certified block above.`

**Why false.** `F5_values` certifies printedQ2 = 0.4167 (5/12) and correctQ2 = 0.2083 (5/24), with the printed − correct
difference 0.2083 (role difference(printed−derived), positive): the printed coefficient is the LARGER one, so the source
OVERstates the term by a factor 2, and the claimed printed/correct values (1/24, 1/12) appear nowhere in the block.
(First attempt with a backticked record name followed by a parenthesis was caught by FB5; the shipped version avoids that
shape.)

**Expected:** all Python checks green after this wording (valid shape: rendering differential; the raw line sits in the notes).
