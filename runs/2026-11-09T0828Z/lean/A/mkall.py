# Concatenate the scratch modules into one file (scratch files are not lake modules).
import re
parts=['NegCrocco.lean','NoCross.lean','UStep.lean','UPrime_body.lean']
imps=[];bodies=[]
for f in parts:
    s=open(f).read()
    lines=s.splitlines()
    im=[l for l in lines if l.startswith('import ')]
    rest=[l for l in lines if not l.startswith('import ') and not l.startswith('#print axioms')]
    for l in im:
        if l not in imps: imps.append(l)
    bodies.append('\n'.join(rest))
out='\n'.join(imps)+'\n'+'\n\n'.join(bodies)+'\n#print axioms Scratch.UPrime.u_prime\n#print axioms Scratch.UPrime.u_equal_shear\n'
open('UPrimeAll.lean','w').write(out)
