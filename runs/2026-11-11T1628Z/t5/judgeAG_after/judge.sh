export PATH=$HOME/.elan/bin:$PATH
cd /home/claude/fzJA
lake build Checked > /tmp/jA_build.log 2>&1; echo "build exit $?"
TRUST_RELOCK=1 lake env lean scripts/trust/StatementDeps.lean > /tmp/jA_sd.log 2>&1; echo "SD exit $?"
python3 scripts/trust/check_necessity.py > /tmp/jA_nec.log 2>&1; echo "NEC exit $?"
date -u +"END %H:%M"
