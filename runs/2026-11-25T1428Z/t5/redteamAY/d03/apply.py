import sys, pathlib
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
from cert_apply import run
run(sys.argv[1], [
 ("CLAUSE","Checked.Cosmography.Aviles.cosmoCoeff","The order 3 coefficient is the jerk parameter usually written j","Checked.Trust.PhraseCerts.cosmoCoeff_two"),
 ("CLAUSE","Checked.Cosmography.Aviles.cosmoCoeff","The order 4 coefficient is the snap parameter usually written s","Checked.Trust.PhraseCerts.cosmoCoeff_two"),
 ("CLAUSE","Checked.Cosmography.Aviles.cosmoCoeff","The order 5 coefficient is the lerk parameter usually written l","Checked.Trust.PhraseCerts.cosmoCoeff_two"),
], "the order 3, 4, 5 lines of `cosmoCoeff`", pathlib.Path(__file__).parent / "gen")
