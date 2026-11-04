import numpy as np
import espace
from scipy.optimize import linprog
base=espace.f
for eta in [0,0.002,0.005,0.01]:
    espace.f=base*(1+eta)
    w=min(espace.lp(Om)[0] for Om in np.linspace(0.2,0.45,11))
    print(eta, round(w,4))
