# julia -p N --project=/path/to/Hecke test_bfs.jl p g
#
# The Jacobian tests of all classes of a finished (or partial) enumeration
# bfs_p{p}_g{g}.state in the current directory (run_bfs.jl with test = false),
# one class per worker process at a time. Updates bfs_p{p}_g{g}.txt,
# .txt.jacobians and .state; can be interrupted and started again.
using Distributed
const SRC = joinpath(@__DIR__, "superspecial_bfs.jl")
include(SRC)
nprocs() > 1 && @everywhere workers() include($SRC)
using Serialization
p = parse(Int, ARGS[1]); g = parse(Int, ARGS[2])
tables_file = joinpath(pwd(), "neighbour_tables_g$(g).jls")
state_file = joinpath(pwd(), "bfs_p$(p)_g$(g).state")
T = load_or_build_tables(g, tables_file)
state = load_state(state_file; tables = T)
println("p = $p, g = $g: $(length(state.classes)) classes, $(count(r -> r.expanded, state.classes)) expanded, " *
        "$(count(r -> r.status == :untested, state.classes)) untested; $(nworkers()) workers"); flush(stdout)
n = test_classes!(state; checkpoint = joinpath(pwd(), "bfs_p$(p)_g$(g).txt"), state_file = state_file)
println("Jacobians: $n")
println("statuses: ", sort(collect(Dict(s => count(r -> r.status == s, state.classes) for s in unique(r.status for r in state.classes)))))
