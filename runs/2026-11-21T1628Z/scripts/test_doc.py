# Advisory: read a draft docstring with V1's word lists against the generated claim of rl19_box_unmatched (same
# definitions and hypotheses as the new headline, minus the box), before the freeze.
import sys; sys.path.insert(0, 'scripts/trust')
import check_claim_vocab as V
doc = open(sys.argv[1]).read()
for full, gen, para in V.sections():
    if full.endswith('rl19_box_unmatched'):
        gv = V.gen_vocab(gen); break
vocab = set(V.words(open('scripts/trust/prose_vocab.txt').read()))
bad = sorted({w for w in V.words(doc) if not (V.forms(w) & (gv | V.FUNCTION | vocab)) and len(w) > 1})
print('not covered:', bad)
