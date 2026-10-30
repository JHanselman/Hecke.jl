#!/bin/bash
# Enumeration (BFS) on one node of Elwetritsch: 1 main process + (cpus - 1)
# workers. Continues from the state file in RUN_DIR, so it can be resubmitted
# (or chained, see submit_chain.sh) until bfs_p{P}_g{G}.DONE exists.
#
#   sbatch --export=ALL,P=11,G=5 elwetritsch_bfs.slurm
#
#SBATCH -J ss-bfs
#SBATCH -N 1
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=16
#SBATCH --mem-per-cpu=5G
#SBATCH -t 2-00:00:00
#SBATCH -o ss-bfs-%j.out
#SBATCH -e ss-bfs-%j.err
#SBATCH --mail-type=END,FAIL
##SBATCH --account=<PROJECT>        # with an AHRP project: higher priority, more nodes

set -uo pipefail
P=${P:-11}
G=${G:-5}
K=${K:-8}
REPO=${REPO:-$HOME/Hecke.jl}
RUN_DIR=${RUN_DIR:-$HOME/superspecial_runs/p${P}_g${G}}
export PATH="$HOME/.juliaup/bin:$PATH"
export JULIA_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1
export BFS_STATE_INTERVAL=${BFS_STATE_INTERVAL:-300}

mkdir -p "$RUN_DIR" && cd "$RUN_DIR"
if [ -f "bfs_p${P}_g${G}.DONE" ]; then
  echo "already done: $(cat bfs_p${P}_g${G}.DONE)"; exit 0
fi
echo "job $SLURM_JOB_ID on $(hostname), $SLURM_CPUS_PER_TASK cpus, $(date)"
julia -p $((SLURM_CPUS_PER_TASK - 1)) --project="$REPO" \
  "$REPO/examples/Superspecial/run_bfs.jl" "$P" "$G" "$K" false >> "bfs_p${P}_g${G}.log" 2>&1
echo "exit $? at $(date)"
