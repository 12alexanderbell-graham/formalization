import sys, json
sys.path.insert(0,'scripts/trust')
import check_literals as L
rows=L.load_rows()
heads={r["name"]:r for r in rows if r.get("type")=="headline"}
errors=[]
consts=L.reader_constants()
readings=L.load_readings(heads,errors)
baseline=L.load_baseline(heads,errors)
L.LOOSE_PAIRS=L.pair_baseline(L.LOOSE_BL)
res=[]
for h,row in heads.items():
    if h not in baseline: continue
    unc,_=L.analyse(row,consts,readings,[],strict=True)
    if not unc: continue
    toks=L.lex(L.statement_text(row["module"],row["name"]))
    for c,const in consts.items():
        if not any(L.is_num(t) for t in const[1]): continue
        if any(c==cc for cc,_ in readings.get(h,[])): continue
        try:
            spans=L.covered_spans(toks,const,True)
        except Exception as e:
            continue
        if spans:
            ok=set()
            for sp in spans:
                for j in sp:
                    if L.is_num(toks[j]): ok.add(j)
            if ok:
                print(h.split('.')[-1],'|',c.split('.')[-1],'|',' '.join(const[1])[:60],'|',len(ok),'of',len(unc), flush=True)
