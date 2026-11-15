import sys, subprocess, pathlib, re
def root():
    return pathlib.Path(sys.argv[1]).resolve()
def edit(R, old, new, count=1):
    p = R/"FINDINGS.md"; t = p.read_text()
    assert t.count(old) >= 1, old[:60]
    p.write_text(t.replace(old, new, count))
def ledger(R, line):
    p = R/"LEDGER.md"; t = p.read_text()
    p.write_text(t.rstrip("\n") + "\n" + line + "\n")
def regen(R):
    for c in (["python3","scripts/trust/check_numbers.py","--write"],["python3","validation/make_packet.py"]):
        subprocess.run(c, cwd=R, check=False, capture_output=True)
LAST = "| C4 | Capozziello, Lazkoz, Salzano 2011 | — | → **F2** |\n"
