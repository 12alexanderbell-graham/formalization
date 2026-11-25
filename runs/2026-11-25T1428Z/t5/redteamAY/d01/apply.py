import sys, pathlib, shutil
root = pathlib.Path(sys.argv[1])
note = root / "runs/2026-11-25T1528Z/referee_note_printedL0.md"
note.parent.mkdir(parents=True, exist_ok=True)
note.write_text("""# Referee note on the printed-L0 witnesses (run 2026-11-25T1528Z)

The referee compared the witness `Checked.Cosmography.AvilesWitness.printedL0_false_at` (module `AvilesWitness`, the
printed L0 coefficient of the flat LambdaCDM series) with the source figure. Finding: the point at which `printedL0_false_at`
evaluates the printed coefficient is not the point the source's table uses; whether the statement says what the source
says is open.
The sibling statement `printedL0_false_at` in module `CPLExistence` was not examined.
""")
p = root / "scripts/trust/objections.txt"
t = p.read_text()
if not t.endswith("\n"): t += "\n"
t += "CPLExistence.printedL0_false_at | 2026-11-25T1528Z | runs/2026-11-25T1528Z/referee_note_printedL0.md | evaluation point of the printed L0 witness queried\n"
p.write_text(t)
l = root / "LEDGER.md"
s = l.read_text()
if not s.endswith("\n"): s += "\n"
s += "- 2026-11-25, run 2026-11-25T1528Z — **Objection entered:** `scripts/trust/objections.txt`: one open objection on a printed-L0 witness, text in `runs/2026-11-25T1528Z/referee_note_printedL0.md`.\n"
l.write_text(s)
for f in ["CLAIMS.md","CLAIMS_READER.md","PHRASE_LINES.md"]:
    g = pathlib.Path(__file__).parent / "gen" / f
    if g.exists(): shutil.copy(g, root / f)
import subprocess
subprocess.run(["python3", "validation/make_packet.py"], cwd=root, check=True, stdout=subprocess.DEVNULL)
