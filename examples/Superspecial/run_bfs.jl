# julia -p N --project=/path/to/Hecke run_bfs.jl p g [k = 8] [test = true]
#
# Complete enumeration of the principally polarized superspecial abelian
# g-folds in characteristic p (BFS in the (2,...,2)-isogeny graph), with N
# worker processes for the neighbours (-p N; without it everything runs in
# one process). Output in the current directory:
#   bfs_p{p}_g{g}.txt (+ .jacobians)   rewritten after every expansion
#   bfs_p{p}_g{g}.state                full state (text), every BFS_STATE_INTERVAL seconds
#                                      (default 600) and at the end; a new run with the
#                                      same p, g continues from it (also on another machine)
#   bfs_p{p}_g{g}.DONE                 written when the enumeration is closed and the
#                                      mass formula holds
#   neighbour_tables_g{g}.jls          the tables (built once, about 6 min for g = 5;
#                                      rebuilt if written by another Julia version)
using Distributed
const SRC = joinpath(@__DIR__, "superspecial_bfs.jl")
include(SRC)
nprocs() > 1 && @everywhere workers() include($SRC)
using Serialization
p = parse(Int, ARGS[1]); g = parse(Int, ARGS[2])
k = length(ARGS) >= 3 ? parse(Int, ARGS[3]) : 8
test = length(ARGS) >= 4 ? parse(Bool, ARGS[4]) : true
println("p = $p, g = $g, GF(p^$k), mass = $(mass(g, p)) ≈ $(Float64(mass(g, p))), $(nworkers()) worker processes"); flush(stdout)

tables_file = joinpath(pwd(), "neighbour_tables_g$(g).jls")
T = load_or_build_tables(g, tables_file)

out = joinpath(pwd(), "bfs_p$(p)_g$(g).txt")
state_file = joinpath(pwd(), "bfs_p$(p)_g$(g).state")
state = if isfile(state_file)
  s = load_state(state_file; tables = T)
  println("continuing: $(length(s.classes)) classes, $(count(r -> r.expanded, s.classes)) expanded"); flush(stdout)
  s
else
  BFSState(p, g; k = k, tables = T)
end
nprocs() > 1 && setup_workers(state, tables_file)
closed = bfs!(state; test = test, checkpoint = out, state_file = state_file,
              state_interval = parse(Float64, get(ENV, "BFS_STATE_INTERVAL", "600")))
result = mass_check(state)
# marker for job chains: the enumeration is finished and certified
if closed && result.consistent && result.complete
  write(joinpath(pwd(), "bfs_p$(p)_g$(g).DONE"), "classes $(length(state.classes)), sum 1/#Aut = $(result.total)\n")
end
