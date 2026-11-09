import sys; sys.path.insert(0, __file__.rsplit("/d02/", 1)[0])
from common import edit
edit(sys.argv[1], [
 ("(integral of one over the scale factor over cosmic time; integrated from emission time to observation time; units",
  "(integral of one over the scale factor over cosmic time from the observation time {t₀} to the emission time {t}; units"),
], "- Reworded the phrase of comoving (integration limits stated with the argument roles).")
