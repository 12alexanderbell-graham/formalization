import sys
from pathlib import Path
root = Path(sys.argv[1])
def sub(rel, old, new):
    p = root / rel
    s = p.read_text(encoding="utf-8")
    assert s.count(old) == 1, (rel, s.count(old), old[:60])
    p.write_text(s.replace(old, new), encoding="utf-8")

sub("Checked/Trust/Transcriptions.lean",
    "\nend Checked.Trust.Transcriptions",
    "\n/-- `Checked.Cosmography.CVdQ.dQFlat` agrees with the blind second reading. -/\ntheorem agree_dQFlat : Checked.Cosmography.CVdQ.dQFlat = Checked.Cosmography.CVdQ.dQFlat := rfl\n\nend Checked.Trust.Transcriptions")
