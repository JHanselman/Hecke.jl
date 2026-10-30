#!/bin/bash
# One-time setup on Elwetritsch (run on a login node, elwe1.rz.rptu.de):
# Julia via juliaup in $HOME (there is no Julia module), the Hecke fork with
# the superspecial code, and the package downloads. Precompilation is CPU
# heavy: do it in a short interactive job (see below), not on the login node.
#
#   bash elwetritsch_setup.sh [branch]
set -euo pipefail
BRANCH=${1:-jh/superspecial}
JULIA_CHANNEL=${JULIA_CHANNEL:-1.12}
REPO=${REPO:-$HOME/Hecke.jl}

# 1. Julia (juliaup installs into ~/.juliaup, packages go to ~/.julia)
if ! command -v juliaup >/dev/null 2>&1 && [ ! -x "$HOME/.juliaup/bin/juliaup" ]; then
  curl -fsSL https://install.julialang.org | sh -s -- --yes --default-channel "$JULIA_CHANNEL"
fi
export PATH="$HOME/.juliaup/bin:$PATH"
juliaup add "$JULIA_CHANNEL" || true
juliaup default "$JULIA_CHANNEL"
julia --version

# 2. The code
if [ ! -d "$REPO" ]; then
  git clone --branch "$BRANCH" https://github.com/JHanselman/Hecke.jl.git "$REPO"
else
  git -C "$REPO" fetch origin && git -C "$REPO" checkout "$BRANCH" && git -C "$REPO" pull --ff-only
fi

# 3. Download the dependencies (no precompilation here)
JULIA_PKG_PRECOMPILE_AUTO=0 julia --project="$REPO" -e 'using Pkg; Pkg.instantiate()'

cat <<MSG

Done. Next, precompile in an interactive job (about 10-20 min), e.g.
  salloc -N 1 -c 8 -t 1:00:00
  srun julia --project=$REPO -e 'using Hecke'
and test on a small case (g = 4, p = 7: 19 classes, a few minutes):
  mkdir -p \$HOME/superspecial_runs/test && cd \$HOME/superspecial_runs/test
  srun julia -p 7 --project=$REPO $REPO/examples/Superspecial/run_bfs.jl 7 4 8 false
The last line must say "equal: true".
MSG
