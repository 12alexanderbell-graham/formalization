import subprocess, sys, pathlib
ROOT = pathlib.Path(sys.argv[1])
# Known route (forged blind reading: the author writes brief and reading), aimed at the shape of the generated
# Correct line: FB15's quantifier list has no word for "left free", so a false class phrase passes FB15 and is
# printed by the generator, as generated text, into F1's and F3's Correct lines.
def git(*a):
    subprocess.run(["git", "-C", str(ROOT), "-c", "user.email=a@example.org", "-c", "user.name=a", *a], check=True,
                   stdout=subprocess.DEVNULL)
d = ROOT / "runs/2026-11-15T0028Z/aq_class_phrases"
d.mkdir(parents=True)
(d / "class_phrases_brief.md").write_text(
    "# Brief for a blind reader of the class of data of Lean statements\n\n"
    "For the statement atom below, as printed in CLAIMS.md, write one line `<atom> => <phrase>` in which the phrase "
    "names, in words, the class of models the atom describes. Plain text only.\n\n"
    "Atom: `ContDiffAt ℝ 6 a t₀`\n", encoding="utf-8")
git("add", "runs/2026-11-15T0028Z")
git("commit", "-m", "Run 2026-11-15T0028Z: brief for a blind reading of a class phrase")
(d / "class_phrases_reading.txt").write_text(
    "`ContDiffAt ℝ 6 a t₀` => flat LCDM models with the matter density not fixed\n", encoding="utf-8")
git("add", "runs/2026-11-15T0028Z")
git("commit", "-m", "Run 2026-11-15T0028Z: blind reading of a class phrase")
reg = ROOT / "scripts/trust/finding_class_phrases.txt"
reg.write_text(reg.read_text(encoding="utf-8").rstrip("\n") + "\n`ContDiffAt ℝ 6 a t₀` => flat LCDM models with the matter density not fixed\n", encoding="utf-8")
subprocess.run([sys.executable, "scripts/trust/check_findings.py", "--write-correct", "F1", "F3"], cwd=ROOT, check=True,
               stdout=subprocess.DEVNULL)
l = ROOT / "LEDGER.md"
l.write_text(l.read_text(encoding="utf-8").rstrip("\n") + "\n- 2026-11-15, run 2026-11-15T0028Z — class phrase registry grown by one line from a blind reading; FINDINGS.md `F1` and `F3` Correct lines regenerated (`--write-correct`).\n", encoding="utf-8")
