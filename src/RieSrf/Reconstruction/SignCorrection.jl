################################################################################
#
#  SignCorrection.jl : the signs of the Schottky-Jung theta constants
#
#  prym_thetas gives the theta constants of the Prym only up to sign. The
#  signs are fixed by Riemann's quartic relations (RiemannRelations.jl):
#
#   - sign changes that do not change the abelian variety span a space of
#     dimension g(2g + 1); the characteristics at the pivots of its echelon
#     form are fixed (find_fixed_even_chars), the other signs are unknowns
#     over GF(2);
#   - a relation is given by a term (a zero-sum tetrad of fixed
#     characteristics) and a symplectic matrix M1; it holds with coefficients
#     +-1, and each coefficient is a linear equation in the unknowns.
#
#  Which pairs (term, M1) give useful relations does not depend on the
#  (generic) curve, so they are found once by a random search (find_sign_data,
#  random elements of the orthogonal group; this part needs Oscar, see
#  Generation/OscarIsometries.jl) and stored (Data/SignDataG*.txt,
#  save_sign_data). correct_signs_with_data! then only evaluates these
#  relations.
#
#  Entry points: correct_signs_with_data!, load_sign_data, save_sign_data,
#  find_sign_data, extend_sign_data, sign_data_coverage.
#
################################################################################

_default_sign_data_file(g::Int) = joinpath(@__DIR__, "Data", "SignDataG$(g).txt")

# The stored sign data of genus g: `data` itself (loaded pairs), a file, or
# the default file
function _loaded_sign_data(data, g::Int)
  data === nothing && return load_sign_data(_default_sign_data_file(g))
  data isa AbstractString && return load_sign_data(data)
  return data
end

################################################################################
#
#  The linear system for the signs
#
################################################################################

# The characteristics whose signs can be chosen (fixed) and the others
function find_fixed_even_chars(g)
  F = GF(2)
  char_vecs = collect.(sort(even_theta_characteristics(g)))
  n = length(char_vecs)
  dim_of_Sp2g = g*(2*g + 1)
  sign_flips = [[one(F) for _ in 1:n]]
  for v in basis(vector_space(F, dim_of_Sp2g))
    T_v = upper_triangular_matrix(v.v[1, :])
    push!(sign_flips, [(transpose(c*T_v)*c) for c in char_vecs])
  end
  A_ech = echelon_form(matrix(sign_flips))
  pivots = [minimum(filter(i -> A_ech[j, i] == one(F), 1:n)) for j in 1:dim_of_Sp2g]
  return [char_vecs[i] for i in pivots], [char_vecs[i] for i in 1:n if !(i in pivots)]
end

# The tetrads {c1, c2, c3, c4} of characteristics in chars with
# c1 + c2 + c3 + c4 = 0 (pairs bucketed by their sum).
function find_zero_sum_tetrads(chars::Vector{Vector{Int}})
  masks = [bitmask(v) for v in chars]
  buckets = Dict{UInt128, Vector{Tuple{Int, Int}}}()
  for i in 1:length(chars) - 1, j in i + 1:length(chars)
    push!(get!(buckets, masks[i] ⊻ masks[j], Tuple{Int, Int}[]), (i, j))
  end
  tetrads = Set{NTuple{4, Int}}()
  for pairs in values(buckets), a in 1:length(pairs) - 1, b in a + 1:length(pairs)
    (i1, j1), (i2, j2) = pairs[a], pairs[b]
    push!(tetrads, Tuple(sort([i1, j1, i2, j2])))
  end
  return [(chars[i], chars[j], chars[k], chars[l]) for (i, j, k, l) in tetrads]
end

function _SignSystem(g::Int, cols::Vector{Int})
  position = Dict(c => k for (k, c) in enumerate(cols))
  return _SignSystem(cols, position, BitVector[], Int[], Bool[], 0)
end

# Adds the equations of a relation that raise the rank; returns whether one
# did. The equation of a term: the sum of the flips of its characteristics is
# (coefficient - 1)/2 mod 2 (fixed characteristics are not flipped).
function _add_relation!(S::_SignSystem, rel)
  added = false
  n = length(S.cols)
  for (mon, coeff) in rel
    v = falses(n)
    for j in mon
      k = get(S.position, j, 0)
      k == 0 || (v[k] = !v[k])
    end
    b = isodd(div(coeff - 1, 2))
    for (row, pivot, r) in zip(S.rows, S.pivots, S.rhs)
      if v[pivot]
        v .⊻= row
        b ⊻= r
      end
    end
    pivot = findfirst(v)
    pivot === nothing && continue
    push!(S.rows, v)
    push!(S.pivots, pivot)
    push!(S.rhs, b)
    S.rank += 1
    added = true
  end
  return added
end

# Solves the system (back substitution; free unknowns 0) and flips the signs
# of the non-fixed thetas.
function _apply_signs!(thetas, S::_SignSystem, non_fixed_thetas)
  x = falses(length(S.cols))
  for k in S.rank:-1:1
    value = S.rhs[k]
    row = S.rows[k]
    for j in findall(row)
      j == S.pivots[k] || (value ⊻= x[j])
    end
    x[S.pivots[k]] = value
  end
  for j in 1:length(S.cols)
    x[j] && (thetas[non_fixed_thetas[j]...] = -thetas[non_fixed_thetas[j]...])
  end
  return thetas
end

# The relation for (term, M1), scaled so that the term has coefficient 1;
# nothing if there is no relation or the term does not occur in it.
_relation_for_pair(g::Int, thetas, term, M1::FqMatrix) = _relation_for_data(thetas, term, _relation_terms_int(g, term, M1))

function _relation_for_data(thetas, term, data)
  # a Vector (as the entries of term_tup): sort of a tuple is a tuple
  fixed_term = sort([char_to_index(collect(c)) for c in term])
  position = findfirst(==(fixed_term), data.term_tup)
  (position === nothing || data.coefficients[position] == 0) && return nothing
  # (theta constants that do not satisfy Riemann's relations, e.g. those of
  # Schottky-Jung for a non-Jacobian, can make LLL fail on huge balls)
  test, rel = try
    _relation_from_terms(thetas, data)
  catch err
    err isa InexactError || rethrow()
    false, nothing
  end
  test || return nothing
  # Riemann's relations have coefficients +-1 (with the sign flips)
  all(x -> abs(x[2]) == 1, rel) || return nothing
  index = findfirst(x -> x[1] == fixed_term, rel)
  index === nothing && return nothing
  s = rel[index][2]
  return [(m, c * s) for (m, c) in rel]
end

# The relations of the pairs, in parallel (threads; the pairs are
# independent, the thetas are only read). The combinatorial data of the
# relations (GF(2) matrices) are computed on the calling thread; the threads
# only evaluate and run LLL.
function _relations_for_pairs(g::Int, thetas, pairs; parallel::Bool = Threads.nthreads() > 1)
  relations = Vector{Any}(undef, length(pairs))
  if parallel
    datas = [_relation_terms_int(g, term, M1) for (term, M1) in pairs]
    Threads.@threads for k in eachindex(pairs)
      relations[k] = _relation_for_data(thetas, pairs[k][1], datas[k])
    end
  else
    for (k, (term, M1)) in enumerate(pairs)
      relations[k] = _relation_for_pair(g, thetas, term, M1)
    end
  end
  return relations
end

# The terms, the non-fixed characteristics whose constant does not vanish,
# and the empty system
function _sign_setup(g::Int, thetas)
  fixed_thetas, non_fixed_thetas = find_fixed_even_chars(g)
  # identically vanishing thetas (non-generic case) carry no sign: balls
  # containing 0, and values below 2^(-prec/2) relative to the largest (e.g.
  # the Schottky-Jung values at a hyperelliptic curve: products of a
  # vanishing and a nonvanishing theta constant, tiny balls not containing 0,
  # whose signs Riemann's relations cannot determine)
  CC = parent(first(values(thetas)))
  largest = maximum(_log2_abs(v) for v in values(thetas))
  negligible(v) = contains(v, zero(CC)) || _log2_abs(v) < largest - precision(CC) / 2
  filter!(c -> !negligible(thetas[c...]), non_fixed_thetas)
  terms = find_zero_sum_tetrads(fixed_thetas)
  return terms, non_fixed_thetas, _SignSystem(g, char_to_index.(non_fixed_thetas))
end

################################################################################
#
#  The random search (needs random isometries, see below)
#
################################################################################

# A function g -> (a function returning a random element of the orthogonal
# group O(g, g) over GF(2), the isometries of the quadratic form x'y), or
# nothing. Hecke has no such groups: Generation/OscarIsometries.jl sets it with
# Oscar's isometry_group.
_random_isometry_sampler = nothing

function _set_random_isometry_sampler!(sampler)
  global _random_isometry_sampler = sampler
  return nothing
end

# Random search until full rank; records the (term, M1) pairs that were used.
# The pairs are drawn in batches (batch_size per thread) and their relations
# computed in parallel; the equations are added in the order of the batch.
function _random_search!(S::_SignSystem, g::Int, thetas, terms, target_rank;
                         pairs = nothing, max_tries::Int = 100000, batch_size::Int = 4,
                         parallel::Bool = Threads.nthreads() > 1, verbose::Bool = false)
  F = GF(2)
  @req _random_isometry_sampler !== nothing "The random search for Riemann relations needs random elements of O(g, g) over GF(2), which Hecke does not provide: run `using Oscar` and include Generation/OscarIsometries.jl (next to this file). (Reached because the stored sign data do not determine all signs.)"
  random_isometry = _random_isometry_sampler(g)
  v1 = F.(ZZ.(max_noether_characteristics(g)[1] * 2))
  to_term = Dict{Any, FqMatrix}()        # map_even_characteristic(v1, term[1]) per term
  tries = 0
  found = 0
  while S.rank < target_rank
    @req tries < max_tries "Random search did not reach full rank ($(S.rank) of $target_rank)."
    batch = Tuple{Any, FqMatrix}[]
    for _ in 1:batch_size * Threads.nthreads()
      term = terms[rand(1:length(terms))]
      M = get!(() -> map_even_characteristic(v1, F.(collect(term[1]))), to_term, term[1])
      push!(batch, (term, random_isometry() * M))
    end
    tries += length(batch)
    for ((term, M1), rel) in zip(batch, _relations_for_pairs(g, thetas, batch; parallel))
      rel === nothing && continue
      found += 1
      if _add_relation!(S, rel) && pairs !== nothing
        push!(pairs, (term, M1))
      end
      S.rank >= target_rank && break
    end
    verbose && println("tries $tries, relations with the term $found, rank $(S.rank) of $target_rank")
  end
  return S
end

@doc raw"""
    find_sign_data(g, thetas; parallel = Threads.nthreads() > 1, verbose = false, kw...)
        -> Vector{Tuple{term, FqMatrix}}

Corrects the signs of the even theta constants `thetas` of genus `g` by the
random search and returns the (term, M1) pairs whose relations were used.
Run it on the theta constants of a generic curve and store the result with
`save_sign_data`. Needs Oscar: include `Generation/OscarIsometries.jl` first.
"""
function find_sign_data(g::Int, thetas; kw...)
  terms, non_fixed_thetas, S = _sign_setup(g, thetas)
  pairs = Tuple{Any, FqMatrix}[]
  _random_search!(S, g, thetas, terms, length(non_fixed_thetas); pairs = pairs, kw...)
  _apply_signs!(thetas, S, non_fixed_thetas)
  return pairs
end

@doc raw"""
    correct_signs_with_data!(thetas, g, pairs; fallback = true, parallel = Threads.nthreads() > 1)
        -> thetas, Bool

Corrects the signs of the even theta constants `thetas` of genus `g` (e.g.
the Prym theta constants, `g = 4` for a genus 5 curve) with the relations of
the stored `pairs` (see `load_sign_data`). Returns the corrected thetas and
whether the pairs alone sufficed. If they do not, the missing equations come
from the random search (with `fallback`; needs Oscar, see find_sign_data),
otherwise an error is raised. The pairs the random search used are appended
to `new_pairs` (a vector).
"""
function correct_signs_with_data!(thetas, g::Int, pairs; fallback::Bool = true,
                                  parallel::Bool = Threads.nthreads() > 1, new_pairs = nothing)
  terms, non_fixed_thetas, S = _sign_setup(g, thetas)
  target_rank = length(non_fixed_thetas)
  # in batches: the stored pairs usually reach full rank before the end
  batch = 8 * Threads.nthreads()
  for start in 1:batch:length(pairs)
    S.rank >= target_rank && break
    chunk = pairs[start:min(start + batch - 1, end)]
    for rel in _relations_for_pairs(g, thetas, chunk; parallel)
      rel === nothing || _add_relation!(S, rel)
      S.rank >= target_rank && break
    end
  end
  sufficient = S.rank >= target_rank
  if !sufficient
    @req fallback "The stored pairs give rank $(S.rank) of $target_rank."
    _random_search!(S, g, thetas, terms, target_rank; parallel, pairs = new_pairs)
  end
  _apply_signs!(thetas, S, non_fixed_thetas)
  return thetas, sufficient
end

@doc raw"""
    sign_data_coverage(g, thetas, pairs) -> NamedTuple

The rank that the relations of `pairs` reach for the theta constants `thetas`
of genus g, the rank needed and the non-fixed characteristics whose sign
the pairs leave free. Does not change `thetas`.
"""
function sign_data_coverage(g::Int, thetas, pairs)
  _, non_fixed_thetas, S = _sign_setup(g, thetas)
  for rel in _relations_for_pairs(g, thetas, pairs)
    rel === nothing || _add_relation!(S, rel)
  end
  free = [non_fixed_thetas[k] for k in 1:length(S.cols) if !(k in S.pivots)]
  return (rank = S.rank, needed = length(non_fixed_thetas), free = free)
end

@doc raw"""
    extend_sign_data(g, thetas, pairs) -> Vector

The stored `pairs` and the pairs that the random search needs on top of them
to correct the signs of `thetas` (genus g; a copy is corrected). Needs Oscar
(see find_sign_data).
"""
function extend_sign_data(g::Int, thetas, pairs)
  added = Tuple{Any, FqMatrix}[]
  correct_signs_with_data!(copy(thetas), g, pairs; new_pairs = added)
  return [pairs; added]
end

################################################################################
#
#  Storage (plain text, see Data/)
#
################################################################################

@doc raw"""
    save_sign_data(file, pairs)

Writes the (term, matrix) pairs of find_sign_data to `file`, one per line:
the term (4 characteristics of 2g bits) and the 2g x 2g matrix over GF(2)
row by row, as strings of bits.
"""
function save_sign_data(file::AbstractString, pairs)
  open(file, "w") do io
    g = div(length(first(pairs[1][1])), 2)
    println(io, "# Sign data of genus $g (load_sign_data): one (term, matrix) pair per line,")
    println(io, "# the term as 4 characteristics of $(2*g) bits, the matrix ($(2*g) x $(2*g) over GF(2)) row by row.")
    for (term, M) in pairs
      bits = join(string.(reduce(vcat, collect.(term))))
      matrix_bits = join(string(lift(ZZ, M[i, j])) for i in 1:nrows(M) for j in 1:ncols(M))
      println(io, bits, " ", matrix_bits)
    end
  end
  return nothing
end

@doc raw"""
    load_sign_data(file) -> Vector{Tuple{term, FqMatrix}}

The (term, matrix) pairs written by save_sign_data. The stored data of genus
4 to 7 are in the folder Data next to this file (_default_sign_data_file).
"""
function load_sign_data(file::AbstractString)
  F = GF(2)
  pairs = Tuple{Any, FqMatrix}[]
  for line in eachline(file)
    (isempty(line) || startswith(line, "#")) && continue
    term_bits, matrix_bits = split(line)
    t = [parse(Int, c) for c in term_bits]
    m = [parse(Int, c) for c in matrix_bits]
    n = isqrt(length(m))
    l = div(length(t), 4)
    term = Tuple(t[(k - 1) * l + 1:k * l] for k in 1:4)
    push!(pairs, (term, matrix(F, n, n, F.(m))))
  end
  return pairs
end
