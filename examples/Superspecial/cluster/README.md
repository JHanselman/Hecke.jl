# Running on Elwetritsch (RPTU)

Elwetritsch is the HPC cluster of RPTU Kaiserslautern-Landau, run within the AHRP. It uses SLURM. Facts
from hpc.rz.rptu.de:

- **Access:** open to all members of RPTU and the AHRP.
  - Employees use their RPTU account. Login nodes: `elwe1.rz.rptu.de` to `elwe4.rz.rptu.de`.
  - Students get access through their supervisor in the access management at am.rz.rptu.de.
  - AHRP members from outside RPTU register through the RARP portal and log in on `elwe1/2.rarp-kl.de`.
- **Projects:** without a project, jobs can only use a subset of 24 nodes. With an AHRP project they get
  higher priority (depending on project size) and most of the cluster, via `--account=<PROJECT>`.
- **Requests:** the docs ask you to request resources (cores, memory, run time) rather than partitions or
  queues.
  - Run times: `short` up to 1:30 h, `normal` up to 2 d, `long` up to 10 d, `extralong` up to 30 d.
  - The `idle` partition can use the whole cluster, but its jobs may be suspended or killed. That is fine
    here because the run resumes from its checkpoint.
- **Nodes:** they are shared between users, but the cores a job gets are dedicated to it. Cores per node:
  - Haswell: 16;
  - Skylake-96: 24;
  - EPYC-256: 16;
  - EPYC-384 and EPYC-768: 32.
- **Software:** modules exist, but **Julia is not among them**. Install it yourself with juliaup into
  `$HOME`.
- **Not documented:** whether compute nodes have internet access. So downloads happen on the login
  node, and precompilation in an interactive job.

## Steps

1. Copy `elwetritsch_setup.sh` to the cluster, or clone the repository, and run
   `bash elwetritsch_setup.sh` on a login node. It installs Julia (channel 1.12 by default; set
   `JULIA_CHANNEL`), clones `JHanselman/Hecke.jl` (branch `jh/superspecial`) to `~/Hecke.jl` and
   downloads the dependencies.
2. Precompile and run the g = 4, p = 7 check in a short interactive job (`salloc -N 1 -c 8 -t 1:00:00`,
   then the commands the script prints). Its last line must say `equal: true`.
3. Start the enumeration, for example g = 5, p = 11 with four chained jobs of up to 2 days each, followed
   by the Jacobian tests:
   ```
   bash ~/Hecke.jl/examples/Superspecial/cluster/submit_chain.sh 11 5 4
   ```
   - Each job runs on one node: 1 main process plus 15 workers (`--cpus-per-task=16`).
   - Memory: `--mem-per-cpu=5G` for the enumeration (each Julia process with Hecke needs about 2.5 GB)
     and `8G` for the tests (the Fay kernels of one test need up to about 5–6 GB).
   - It continues from `~/superspecial_runs/p11_g5/bfs_p11_g5.state`.
   - Jobs that start after the enumeration is finished exit at once, because `bfs_p11_g5.DONE` exists.
   - With a project, add `#SBATCH --account=...`. To use the larger EPYC nodes, raise
     `--cpus-per-task` to 32.
4. Follow the progress:
   ```
   squeue -u $USER
   tail ~/superspecial_runs/p11_g5/bfs_p11_g5.log
   ```
   Hits go to `bfs_p11_g5.txt.jacobians`.

The state file is plain text, so you can copy it to your own machine and continue or analyse it there.
