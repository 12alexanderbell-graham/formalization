"""Writes Work/Math/LE32CellQ.lean: the Boolean cells of index three halves (header written here;
chain lemmas transcribed from Checked/Math/LENCellQ.lean with the field of index three halves)."""
import re, sys
src = open(sys.argv[1]).read()   # Checked/Math/LENCellQ.lean (with chainOK/segOK n removed)
i = src.index("/-- Consecutive cells meet")
rest = src[i:]
rest = rest.replace("(n : ℕ) ", "").replace("{n : ℕ} ", "")
for a in ["cellOK", "chainTo", "chainOK", "segOK"]:
    rest = rest.replace(a + " n T", a + " T")
rest = rest.replace("cell_q n c", "cell_q c").replace("cell_facts n c", "cell_facts c").replace("chain_gen n l c", "chain_gen l c")
rest = rest.replace("θ t ^ n", "g32 (θ t)")
rest = rest.replace("end Checked.Math.LENCellQ\n\nnamespace Checked.Math.LENCellQ\nopen Set\n", "")
rest = rest.replace("end Checked.Math.LENCellQ", "end Work.Math.LE32CellQ")
bad = [l for l in rest.split("\n") if " n " in l or "^ n" in l]
assert not bad, bad
hdr = open(sys.argv[2]).read()
open('Work/Math/LE32CellQ.lean', 'w').write(hdr + rest)
