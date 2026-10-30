"""Cattoen & Visser, 'Cosmographic Hubble fits to the supernova data', arXiv:0809.0537 (PRD 78 (2008) 063501).
Transcribed via WebFetch of arxiv.org/pdf (term lists). Same conventions as cv2007.py (Omega_0 = 1 + kc^2/(H0 a0)^2).
Equations are term-for-term identical to 0710.1887; map eq numbers."""
from cv2007 import P as P07
from common import compare
MAP = {'eq3':'eq2 dL(z) k-form','eq14':'eq20 dL(z)','eq15':'eq21 dF(z)','eq16':'eq22 dP(z)','eq17':'eq23 dQ(z)','eq18':'eq24 dA(z)',
       'eq19':'eq25 mu (bracket)','eq20':'eq26 ln dL/z','eq21':'eq27 ln dF/z','eq22':'eq28 ln dP/z','eq23':'eq29 ln dQ/z','eq24':'eq30 ln dA/z',
       'eq29':'eq52 dL(y)','eq30':'eq57 dF(y)','eq31':'eq58 dP(y)','eq32':'eq59 dQ(y)','eq33':'eq60 dA(y)',
       'eq34':'eq61 ln dL/y','eq35':'eq62 ln dF/y','eq36':'eq63 ln dP/y','eq37':'eq64 ln dQ/y','eq38':'eq65 ln dA/y'}
for k_,v in MAP.items():
    pr,rf,var,n = P07[v]; compare('CV2008fits %s (=0710.1887 %s)'%(k_,v.split()[0]), pr, rf, var, n)
