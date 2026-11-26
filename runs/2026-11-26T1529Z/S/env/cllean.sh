#!/bin/bash
# lean with Mathlib + the closure output dir on the path
source <(grep '^export LEAN_PATH' /tmp/claude-0/-home-claude-formalization/32a3656a-fe82-5bab-a882-acf48c963df6/scratchpad/blindlean.sh)
export LEAN_PATH="$LEAN_PATH:/tmp/claude-0/-home-claude-formalization/32a3656a-fe82-5bab-a882-acf48c963df6/scratchpad/cl"
exec /root/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean "$@"
