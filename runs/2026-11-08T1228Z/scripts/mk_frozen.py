"""Emit Work/FalknerSkan/Bounded.lean (frozen statements, proofs = sorry) from lean/Headlines.part."""
import pathlib, re
R = pathlib.Path(__file__).resolve().parent.parent
src = (R / "lean/Headlines.part").read_text(encoding="utf-8")
hdr = (R / "scripts/bounded_header.lean.txt").read_text(encoding="utf-8")
names = ["hiemenz_bounded_window", "homann_bounded_window", "hiemenz_bounded_unique",
         "homann_bounded_unique", "hiemenz_exists_bounded", "homann_exists_bounded"]
blocks = []
for n in names:
    ms = re.findall(r"(/--(?:(?!/--).)*?-/\ntheorem " + n + r"\b.*?):=(?: by)?\n", src, re.S)
    assert len(ms) == 1, n
    blocks.append(ms[0].rstrip() + " := by\n  sorry\n")
out = hdr + "\n".join(blocks) + "\nend Work.FalknerSkan.Bounded\n"
for p in ["Work/FalknerSkan/Bounded.lean"]:
    (R.parent.parent / p).write_text(out, encoding="utf-8")
(R / "lean/Bounded_frozen.lean").write_text(out, encoding="utf-8")
print("ok")
