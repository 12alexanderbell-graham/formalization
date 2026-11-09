import sys; sys.path.insert(0, __file__.rsplit("/d01/", 1)[0])
from common import edit
edit(sys.argv[1], [
 ("the dust matter density at the time of evaluation {t} for the present matter density parameter {Ω} and the present time {t₀} with the scale factor {a}",
  "the dust matter density at the present time {t₀} for the present matter density parameter {Ω} and the time of evaluation {t} with the scale factor {a}"),
 ("holds at the time of evaluation {t} for the present matter density parameter {Ω}, the scale factor {a}, the gravity Lagrangian function of Ricci scalar {F} and the present time {t₀} (constraint equation",
  "holds at the present time {t₀} for the present matter density parameter {Ω}, the scale factor {a}, the gravity Lagrangian function of Ricci scalar {F} and the time of evaluation {t} (constraint equation"),
], "- Reworded the phrases of rhoM and FriedmannEq (word order of the argument list only).")
