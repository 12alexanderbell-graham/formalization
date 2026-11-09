import sys; sys.path.insert(0, __file__.rsplit("/d03/", 1)[0])
from common import edit
edit(sys.argv[1], [
 ("({n}-th time derivative of the scale factor over the scale factor divided by the {n}-th power of the Hubble rate;",
  "({n}-th time derivative of the scale factor over the scale factor;"),
], "- Shortened the phrase of cosmoCoeff.")
