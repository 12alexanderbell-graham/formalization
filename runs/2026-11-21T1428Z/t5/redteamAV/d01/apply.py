#!/usr/bin/env python3
import sys,re,pathlib
root=pathlib.Path(sys.argv[1])
H='Checked.Data.Moresco16.oL_bic_exceeds'; SHORT='oL_bic_exceeds'; SUMMARY='referee verdict STANDS after a blind re-read of the source table; the statement agrees with the source in every hypothesis and constant, objection closed'; LED='Run 2026-11-21T1628Z, objection record: referee verdict on oL_bic_exceeds entered in objections.txt.'
none_txt="open fidelity objections on record (`scripts/trust/objections.txt`, where every objection to the meaning of a listed headline is entered when it is first written anywhere): none"
new_txt="OPEN FIDELITY OBJECTIONS on record (`scripts/trust/objections.txt`): 1: raised in run 2026-11-21T1628Z, written in `LEDGER.md`: «"+SUMMARY+"»"
with open(root/"scripts/trust/objections.txt","a") as f: f.write(H+" | 2026-11-21T1628Z | LEDGER.md | "+SUMMARY+"\n")
with open(root/"LEDGER.md","a") as f: f.write("- 2026-11-21, "+LED+"\n")
for fn in ("CLAIMS.md","CLAIMS_READER.md"):
    p=root/fn; t=p.read_text()
    i=t.index("\n## `"+SHORT+"`\n"); j=t.index(none_txt,i)
    nxt=t.find("\n## `",i+5)
    assert nxt==-1 or j<nxt
    t=t[:j]+new_txt+t[j+len(none_txt):]
    p.write_text(t)
