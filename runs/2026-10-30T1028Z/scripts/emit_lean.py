import json,re
d=json.load(open('polys.json'))
sig='(q j s l k x : ℝ)'
def lean(e): return e.replace('^','^')
docs={'B4':'Degree-4 truncation of `1/A`.','C5':'`A B4 = 1 + x⁵ C5`.','P5':'`∫₀ˣ B4`: `a₀ H₀ χ` to fifth order.',
 'P5q':'`P5 = x P5q`.'}
out=[]
for kname in ['B4','C5','P5','P5q','M2','WM2','M3','WM3','M4','WM4','M5','WM5','N2','WN2','N3','WN3','N4','WN4','N5','WN5','Wf']:
    doc=docs.get(kname)
    if doc is None:
        if kname[0]=='M': doc=f'Degree-5 truncation of `P5^{kname[1]}`.'
        elif kname[0]=='N': doc=f'Degree-5 truncation of `(1 − A)^{kname[1]}`.'
        elif kname=='Wf': doc='`A · Spoly = Fpoly + x⁶ Wf`.'
        else: doc='Product remainder (`… = … + x⁶ ·`).'
    out.append(f'/-- {doc} -/\nnoncomputable def {kname} {sig} : ℝ :=\n  {d[kname]}\n')
open('algebra.lean','w').write('\n'.join(out))
