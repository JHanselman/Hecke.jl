################################################################################
#
#  SignCorrectionFromMatrices.jl : sign correction of theta constants with
#  precomputed (term, matrix) pairs
#
#  The sign correction of SignCorrection.jl draws random elements T of the
#  isometry group and keeps the relations relation_with_term(g, thetas, term,
#  T) that contain the term (a zero-sum tetrad of fixed characteristics). The
#  relation only depends on the term and on M1 = T * M, M =
#  map_even_characteristic(Max Noether characteristic, term[1]). The
#  characteristics in a relation do not depend on the curve, so the pairs
#  (term, M1) found once (find_sign_data, with the random search) can be
#  reused (correct_signs_with_data!): only the coefficients of the relations,
#  which carry the sign information, are computed numerically. If the stored
#  pairs do not reach full rank (non-generic curve), the random search takes
#  over.
#
#  Entry points: find_sign_data, save_sign_data, load_sign_data,
#  correct_signs_with_data!.
#  Uses RiemannRelations.jl (relation_with_term, max_noether_characteristics,
#  bitmask), ReconstructCurveAuxiliary.jl (map_even_characteristic). Saving and
#  loading need Oscar.
#
################################################################################

# The sign changes of the even theta constants that do not change the curve
# (a common sign and (-1)^(c^T T c), T upper triangular) span a space of
# dimension g(2g + 1); the characteristics at the pivots of its echelon form
# are fixed (their signs can be chosen), the signs of the others are
# determined by Riemann's relations.
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

# State of the GF(2) system for the sign flips x of the non-fixed thetas,
# kept in echelon form while the equations are added (one reduction per
# equation instead of a rank computation): row k has its pivot at pivots[k]
# and zeros at the pivots of the earlier rows.
mutable struct _SignSystem
  cols::Vector{Int}                # theta indices of the non-fixed characteristics
  position::Dict{Int, Int}         # theta index -> unknown 1..length(cols)
  rows::Vector{BitVector}          # the equations (coefficients of x), echelon form
  pivots::Vector{Int}              # the pivot of each row
  rhs::Vector{Bool}                # the right hand sides
  rank::Int                        # number of rows
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

# The relation for (term, M1) (M1 = T M as returned by relation_with_term),
# scaled so that the term has coefficient 1; nothing if there is no relation
# or the term does not occur in it. The characteristics are checked first, so
# the theta constants and LLL are only used when the term occurs.
function _relation_for_pair(g::Int, thetas, term, M1::FqMatrix)
  data = _relation_terms_int(g, term, M1)
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
# independent, the thetas are only read). The random matrices are drawn
# before, on the calling thread (rand on the GAP group is not thread safe).
function _relations_for_pairs(g::Int, thetas, pairs; parallel::Bool = Threads.nthreads() > 1)
  relations = Vector{Any}(undef, length(pairs))
  if parallel
    Threads.@threads for k in eachindex(pairs)
      local term, M1 = pairs[k]
      relations[k] = _relation_for_pair(g, thetas, term, M1)
    end
  else
    for (k, (term, M1)) in enumerate(pairs)
      relations[k] = _relation_for_pair(g, thetas, term, M1)
    end
  end
  return relations
end

function _sign_setup(g::Int, thetas)
  fixed_thetas, non_fixed_thetas = find_fixed_even_chars(g)
  # identically vanishing thetas (non-generic case) carry no sign
  filter!(c -> !contains(thetas[c...], zero(parent(thetas[c...]))), non_fixed_thetas)
  terms = find_zero_sum_tetrads(fixed_thetas)
  return terms, non_fixed_thetas, _SignSystem(g, char_to_index.(non_fixed_thetas))
end

# Random search until full rank; records the (term, M1) pairs that were used.
# The pairs are drawn in batches (batch_size per thread) and their relations
# computed in parallel; the equations are added in the order of the batch.
function _random_search!(S::_SignSystem, g::Int, thetas, terms, target_rank;
                         pairs = nothing, max_tries::Int = 100000, batch_size::Int = 4,
                         parallel::Bool = Threads.nthreads() > 1, verbose::Bool = false)
  F = GF(2)
  G = isometry_group(quadratic_form([zero_matrix(F, g, g) identity_matrix(F, g); zero_matrix(F, g, g) zero_matrix(F, g, g)]))
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
      push!(batch, (term, matrix(rand(G)) * M))
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
random search and returns the (term, M1) pairs whose relations were used
(each contributed at least one equation). Run on a generic curve; the result
is for `save_sign_data`. With `parallel` the relations are computed on all
threads (start Julia with `-t n`); `verbose` prints the progress after each
batch; `max_tries`, `batch_size` (pairs per thread and batch): see
_random_search!.
"""
function find_sign_data(g::Int, thetas; kw...)
  terms, non_fixed_thetas, S = _sign_setup(g, thetas)
  pairs = Tuple{Any, FqMatrix}[]
  _random_search!(S, g, thetas, terms, length(non_fixed_thetas); pairs = pairs, kw...)
  _apply_signs!(thetas, S, non_fixed_thetas)
  return pairs
end

@doc raw"""
    correct_signs_with_data!(thetas, g, pairs; fallback = true, parallel = Threads.nthreads() > 1) -> thetas, Bool

Corrects the signs of the even theta constants `thetas` of genus `g` (e.g.
the Prym theta constants, g = 4 for a genus 5 curve) with the relations of
the stored pairs (see `load_sign_data`). Returns the corrected thetas and
whether the pairs alone sufficed; with `fallback = true` missing equations
come from the random search, otherwise an error is raised. With `parallel`
the relations are computed on all threads. The pairs the random search used
are appended to `new_pairs` (a vector, see extend_sign_data).
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

The rank that the relations of the stored `pairs` reach for the theta
constants `thetas` of genus g, the rank needed (the number of non-fixed
even characteristics whose constant does not vanish) and the non-fixed
characteristics whose sign the pairs leave free (the free unknowns of the
echelon form; one of them per missing rank). Does not change `thetas`.
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

The stored `pairs` and the pairs that the random search needs on top of
them to correct the signs of `thetas` (genus g; a copy is corrected). For
sign data that was made on a curve with a vanishing (or numerically zero)
theta constant, whose sign the stored relations then never determine; save
the result with save_sign_data.
"""
function extend_sign_data(g::Int, thetas, pairs)
  added = Tuple{Any, FqMatrix}[]
  correct_signs_with_data!(copy(thetas), g, pairs; new_pairs = added)
  return [pairs; added]
end

# Storage: the terms as flat integer vectors (4 characteristics of length 2g)
# and the matrices as 0/1 integer vectors, so the file does not depend on the
# GF(2) parent or on the order in which find_zero_sum_tetrads returns terms.
function save_sign_data(file::AbstractString, pairs)
  terms = [reduce(vcat, collect.(term)) for (term, _) in pairs]
  mats = [[Int(lift(ZZ, M[i, j])) for i in 1:nrows(M) for j in 1:ncols(M)] for (_, M) in pairs]
  save(file, (terms, mats))
end

function load_sign_data(file::AbstractString)
  data = load(file)
  # the older files (find_correcting_matrices) hold only the matrices, without
  # the terms they belong to; the relations cannot be recovered from them
  @req data isa Tuple && length(data) == 2 "$file is not in the format of save_sign_data (terms and matrices); an older file with only the matrices? Regenerate it with find_sign_data and save_sign_data."
  terms, mats = data
  F = GF(2)
  pairs = Tuple{Any, FqMatrix}[]
  for (t, m) in zip(terms, mats)
    n = isqrt(length(m))
    l = div(length(t), 4)
    term = Tuple(collect(t[(k - 1) * l + 1:k * l]) for k in 1:4)
    push!(pairs, (term, matrix(F, n, n, F.(m))))
  end
  return pairs
end
