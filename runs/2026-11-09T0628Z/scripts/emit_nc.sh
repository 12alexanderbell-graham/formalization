#!/bin/sh
# Emit Checked/Trust/Necessity.lean from the generators and the fixed parts (run 2026-11-09T0628Z).
cd "$(dirname "$0")"
{ cat head.lean; cat profile_body.lean; cat Lin2.lean; echo; python3 gen_nc.py wit; python3 gen_nc.py eqwit; python3 gen_nc.py xwit; python3 gen_y.py wit; echo 'end Checked.Trust.NC'; } > ../../../Checked/Trust/Necessity.lean
