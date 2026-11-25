import sys, pathlib
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
from cert_apply import run
run(sys.argv[1], [
 ("CLAUSE","Checked.Cosmography.Aviles.IsFlatLCDM","spatially flat universe with dust and a cosmological constant","Checked.Trust.PhraseCerts.flatLCDM_expanding"),
 ("CLAUSE","Checked.Cosmography.CPL.IsFlatCPL","spatially flat universe with dust and separately conserved dark energy","Checked.Trust.PhraseCerts.flatCPL_expanding"),
], "the model lines of `IsFlatLCDM` and `IsFlatCPL`", pathlib.Path(__file__).parent / "gen")
