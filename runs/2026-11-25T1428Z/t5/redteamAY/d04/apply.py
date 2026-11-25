import sys, pathlib, shutil
root = pathlib.Path(sys.argv[1])
note = root / "runs/2026-11-25T1528Z/referee_note_lookback.md"
note.parent.mkdir(parents=True, exist_ok=True)
note.write_text("""# Referee note on `lookback_second_order_bigO` (run 2026-11-25T1528Z)

The referee compared `lookback_second_order_bigO` with the second-order lookback expansion of the source and restated
it blind. The restatement agrees with the Lean statement in every term; the verdict is STANDS and the earlier query
about the hypothesis `ContDiffAt ℝ 3 a t₀` is withdrawn.
""")
p = root / "scripts/trust/objections.txt"
t = p.read_text()
if not t.endswith("\n"): t += "\n"
t += "Cosmography.lookback_second_order_bigO | 2026-11-25T1528Z | runs/2026-11-25T1528Z/referee_note_lookback.md | hypothesis smoothness query on the lookback O(z^3) remainder\n"
p.write_text(t)
l = root / "LEDGER.md"
s = l.read_text()
if not s.endswith("\n"): s += "\n"
s += "- 2026-11-25, run 2026-11-25T1528Z — **Objection entered:** `scripts/trust/objections.txt`: one entry on `lookback_second_order_bigO`, text in `runs/2026-11-25T1528Z/referee_note_lookback.md`.\n"
l.write_text(s)
for f in ["CLAIMS.md","CLAIMS_READER.md","PHRASE_LINES.md"]:
    g = pathlib.Path(__file__).parent / "gen" / f
    if g.exists(): shutil.copy(g, root / f)
