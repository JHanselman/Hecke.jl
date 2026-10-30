#!/bin/bash
# Submits N consecutive BFS jobs (each starts when the previous one ended,
# whatever the reason) and then the Jacobian tests:
#   bash submit_chain.sh 11 5 4        # p g number_of_bfs_jobs
set -euo pipefail
P=$1; G=$2; N=${3:-3}
DIR=$(cd "$(dirname "$0")" && pwd)
prev=$(sbatch --parsable --export=ALL,P=$P,G=$G "$DIR/elwetritsch_bfs.slurm")
echo "bfs job $prev"
for i in $(seq 2 "$N"); do
  prev=$(sbatch --parsable --dependency=afterany:$prev --export=ALL,P=$P,G=$G "$DIR/elwetritsch_bfs.slurm")
  echo "bfs job $prev"
done
t=$(sbatch --parsable --dependency=afterany:$prev --export=ALL,P=$P,G=$G "$DIR/elwetritsch_test.slurm")
echo "test job $t (runs after the last bfs job; tests whatever has been enumerated)"
