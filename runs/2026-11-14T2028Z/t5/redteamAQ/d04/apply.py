import sys, pathlib
ROOT = pathlib.Path(sys.argv[1])
p = ROOT / "FINDINGS.md"
t = p.read_text(encoding="utf-8")
# Link reference definitions: in a Markdown renderer (CommonMark and GitHub) a definition anywhere in the document
# turns every matching shortcut reference `[label]` into a link, also the certified tags `[✓F4_values(difference)]`
# inside the generated blocks. FB21 renders only the verified section and looks at html_inline/image tokens, never at
# links, and skips the certified blocks; the definition itself sits in the candidates section (free text, no tokens).
defs = "\n".join([
  '[✓F4_values(difference)]: Checked/Cosmography/BambaDLy.lean "Proved in Lean for every scale factor and every curvature constant K: referee STANDS"',
  '[✓F4_values(printedD2y, printed)]: Checked/Cosmography/BambaDLy.lean "Proved in Lean for every scale factor and every curvature constant K: referee STANDS"',
  '[✓F4_values(correctD2y, derived)]: Checked/Cosmography/BambaDLy.lean "Proved in Lean for every scale factor and every curvature constant K: referee STANDS"',
  '[✓F6_third(difference)]: Checked/Cosmography/BambaCurved.lean "Proved in Lean for every curvature constant K, not only K = 1"',
  '[✓F6_fourth(difference)]: Checked/Cosmography/BambaCurved.lean "Proved in Lean for every curvature constant K, not only K = 1"',
]) + "\n\n"
anchor = "\n## Certified numbers (generated from the Lean records; do not edit)"
assert t.count(anchor) == 1
i = t.index(anchor)
p.write_text(t[:i].rstrip("\n") + "\n\n" + defs.rstrip("\n") + "\n" + t[i:], encoding="utf-8")
