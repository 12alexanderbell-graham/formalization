# Generates Checked/Trust/Transcriptions.lean from Checked/Trust/SecondReading.lean (run 2228Z).
import re
body=open('Checked/Trust/SecondReading.lean').read()
defs=re.findall(r'noncomputable def (\w+)\s*\(([^)]*)\)', body)
ns={'D1':'CCS','D2':'CCS','D3':'CCS','printedD4':'CCS','D1y':'BambaY','printedD2y':'BambaY',
'printedD3y':'BambaK','printedD4y':'BambaK','DA1':'BambaA','DA2':'BambaA','printedDA3':'BambaA','printedDA4':'BambaA',
'printedQ2':'CVdQ','demDL4':'DemianskiZ','demDA4':'DemianskiZ'}
for n in ['DL1z','DL2z','DL3z','printedDL4z','DA1z','DA2z','DA3z','printedDA4z']: ns[n]='BambaZ'
for n,args in defs:
    vs=args.split(':')[0].split()
    full=f'Checked.Cosmography.{ns[n]}.{n}'
    print(f'''/-- `{full}` agrees with the blind second reading. -/
theorem agree_{n} : {full} = Checked.Trust.SecondReading.{n} := by
  funext {' '.join(vs)}
  simp only [{full}, Checked.Trust.SecondReading.{n}] <;> ring
''')
