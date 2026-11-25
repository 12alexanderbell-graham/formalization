# usage: template; DEFECT-specific list of (kind, defn, line, theorem, baseline_line)
import sys, pathlib, shutil
def run(root, certs, ledger_name, gen_dir):
    root = pathlib.Path(root)
    pc = root / "scripts/trust/phrase_certs.txt"
    t = pc.read_text()
    if not t.endswith("\n"): t += "\n"
    bl = root / "scripts/trust/phrase_cert_baseline.txt"
    b = bl.read_text()
    for kind, d, line, th in certs:
        t += f"CERT | {kind} | {d} | {line} | {th}\n"
        old = f"{kind} | {d} | {line}\n"
        assert b.count(old) == 1, old
        b = b.replace(old, "")
    pc.write_text(t); bl.write_text(b)
    l = root / "LEDGER.md"
    s = l.read_text()
    if not s.endswith("\n"): s += "\n"
    s += f"- 2026-11-25, run 2026-11-25T1528Z — **Phrase certificates:** `scripts/trust/phrase_certs.txt`: certificate(s) added for {ledger_name}; the same lines leave `scripts/trust/phrase_cert_baseline.txt`.\n"
    l.write_text(s)
    for f in ["CLAIMS.md","CLAIMS_READER.md","PHRASE_LINES.md"]:
        g = pathlib.Path(gen_dir) / f
        if g.exists(): shutil.copy(g, root / f)
