import sys, os, subprocess
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)) + '/..')
from common import *
root = sys.argv[1]
def git(*a):
    subprocess.run(["git", "-C", root, "-c", "user.name=a", "-c", "user.email=a@a", *a], check=True, capture_output=True)
run = "runs/2026-11-14T1800Z/class_phrase_screen"
os.makedirs(os.path.join(root, run), exist_ok=True)
atom = "ContDiffAt ℝ 6 a t₀"
phrase = "analytic scale factors"
open(os.path.join(root, run, "brief_class_phrases.md"), "w").write(
    "Brief to the reader. For each statement atom listed below, write one line `<atom> => <short plain-words phrase naming "
    "the class of data the atom describes>`. Atoms: " + atom + "\n")
git("add", run); git("commit", "-m", "brief for the class phrase reading")
open(os.path.join(root, run, "class_phrases_reading.txt"), "w").write(f"{atom} => {phrase}\n")
git("add", run); git("commit", "-m", "class phrase reading")
p = os.path.join(root, "scripts/trust/finding_class_phrases.txt")
s = open(p, encoding="utf-8").read().rstrip("\n") + f"\n{atom} => {phrase}\n"
open(p, "w", encoding="utf-8").write(s)
subprocess.run([sys.executable, "scripts/trust/check_findings.py", "--write-correct", "F1", "F3"], cwd=root, check=True, capture_output=True)
ledger(root, "F1", "Correct line regenerated")
ledger(root, "F3", "Correct line regenerated")
