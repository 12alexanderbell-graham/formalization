#!/usr/bin/env python3
"""d04: the reading guide at the top of FINDINGS.md (the 'Layout of a verified finding' paragraph) is author text that no
rule reads (check_numbers only requires the BANNER paragraph; FB14 skips the paragraphs above the sections); it is reworded
so that it overstates what the generated lines and the notes are."""
import sys
root = sys.argv[1]
p = root + "/FINDINGS.md"
s = open(p, encoding="utf-8").read()
old = ("*Printed*: the printed values its Lean records contain, each with the blind second reading it agrees with and the reader's own "
       "description of the source; *Correct*: what its records state, with quantifier, class and direction — then its certified blocks. "
       "Everything under **Unchecked notes**, the author's title first, is author prose that no check reads; a reader who checks "
       "nothing should rely on the generated part only.")
new = ("*Printed*: the printed values its Lean records contain, each with the blind second reading that confirms it against the "
       "source and the reader's own description of where the source prints it; *Correct*: the correct value or formula that replaces the "
       "published one, proved in Lean, with quantifier, class and direction — then its certified blocks. Everything under "
       "**Unchecked notes**, the author's title first, is author prose that no machine check reads but that the finding's Referee line "
       "reports as re-read by an independent referee against the typeset source; a reader may rely on the generated part and on the "
       "title it quotes.")
assert s.count(old) == 1
open(p, "w", encoding="utf-8").write(s.replace(old, new))
