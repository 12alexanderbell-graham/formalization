import sys; sys.path.insert(0, __file__.rsplit("/d05/", 1)[0])
from common import edit
edit(sys.argv[1], [

 ("; the order 2 coefficient is minus the deceleration parameter usually written q; the order 3 coefficient is the jerk parameter usually written j;",
  "; q j s l for the orders 2 3 4 5; the order 3 coefficient is the jerk parameter usually written j;"),
], "- Reworded the phrase of cosmoCoeff (symbols of the coefficients).",
 reg=[("CLAUSE | Checked.Cosmography.Aviles.cosmoCoeff | The order 5 coefficient is the lerk parameter usually written l",
       "CLAUSE | Checked.Cosmography.Aviles.cosmoCoeff | q j s l for the orders 2 3 4 5")])
