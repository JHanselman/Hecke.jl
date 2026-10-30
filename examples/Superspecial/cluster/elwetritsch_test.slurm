#!/bin/bash
# The Jacobian tests of all classes of an enumeration (after
# elwetritsch_bfs.slurm), one class per worker at a time. Can be resubmitted:
# tested classes are kept in the state file.
#
#   sbatch --export=ALL,P=11,G=5 elwetritsch_test.slurm
#
#SBATCH -J ss-test
#SBATCH -N 1
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=16
#SBATCH --mem-per-cpu=8G
#SBATCH -t 2-00:00:00
#SBATCH -o ss-test-%j.out
#SBATCH -e ss-test-%j.err
#SBATCH --mail-type=END,FAIL
##SBATCH --account=<PROJECT>

set -uo pipefail
P=${P:-11}
G=${G:-5}
REPO=${REPO:-$HOME/Hecke.jl}
RUN_DIR=${RUN_DIR:-$HOME/superspecial_runs/p${P}_g${G}}
export PATH="$HOME/.juliaup/bin:$PATH"
export JULIA_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1
cd "$RUN_DIR"
julia -p $((SLURM_CPUS_PER_TASK - 1)) --project="$REPO" \
  "$REPO/examples/Superspecial/test_bfs.jl" "$P" "$G" >> "test_p${P}_g${G}.log" 2>&1
echo "exit $? at $(date)"
