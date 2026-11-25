import sys, pathlib
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
from cert_apply import run
run(sys.argv[1], [
 ("SIGN","Checked.Sim.Duffing.IsDuffingSolution","restoring force for positive stiffness, acceleration equals minus force terms","Checked.Trust.PhraseCerts.duffing_initial"),
 ("CLAUSE","Checked.Sim.Duffing.IsDuffingSolution","the second derivative plus k times x plus β times x cubed vanishes","Checked.Trust.PhraseCerts.duffing_initial"),
], "the equation-of-motion lines of `IsDuffingSolution`", pathlib.Path(__file__).parent / "gen")
