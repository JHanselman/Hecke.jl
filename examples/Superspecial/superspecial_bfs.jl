################################################################################
#
#  superspecial_bfs.jl : complete enumeration of the principally polarized
#  superspecial abelian varieties of dimension g in characteristic p by a
#  breadth-first search in the (2,...,2)-isogeny graph (connected), in theta
#  coordinates.
#
#  Fast neighbour kernel: for each Lagrangian G of GF(2)^2g (all of them,
#  enumerated once) the 2^g characteristics m with M_G . m = (c; 0) and the
#  8th roots of unity of Igusa's formula are tabulated. A neighbour then
#  costs 2^g x 2^g multiplications (t[c] t[c+a]) and 2^g Walsh-Hadamard
#  transforms of length 2^g:
#      theta_A[a; b]^2 = sum_c (-1)^(b.c) t[c] t[c + a],  t[c] = zeta^phase theta[m_c].
#  Isomorphism classes: the key of theta_A^8 = (theta_A^2)^4 (no square
#  roots or signs needed). Only the classes that are expanded need signed
#  theta constants: square roots, signs (fixed characteristics among the
#  nonvanishing ones, relations with any nonvanishing reference term), checked
#  by the dual isogeny back to the parent (the free signs, if any, are chosen
#  by this check).
#
#  Theta constants are vectors indexed by the characteristic as a bit mask
#  (bit i - 1 for entry i of (a_1..a_g, b_1..b_g)), offset 1.
#
################################################################################

include(joinpath(@__DIR__, "superspecial.jl"))
include(joinpath(@__DIR__, "signs_fix.jl"))

const _popc = count_ones

# --- characteristics as masks ---------------------------------------------------

_mask(c) = sum(Int(c[i]) << (i - 1) for i in eachindex(c))
_tuple(m::Int, g::Int) = RSM._char_from_mask(m, g)
theta_vector(thetas::Dict, g::Int) = [thetas[_tuple(m, g)] for m in 0:4^g - 1]
theta_dict(v::Vector, g::Int) = Dict(_tuple(m, g) => v[m + 1] for m in 0:4^g - 1)

function _symplectic_pairing_mask(x::Int, y::Int, g::Int)
  low = (1 << g) - 1
  return isodd(_popc((x & low) & (y >> g)) + _popc((x >> g) & (y & low)))
end

# --- all Lagrangians of GF(2)^2g ------------------------------------------------

@doc raw"""
    all_lagrangians(g) -> Vector{Vector{Int}}

All maximal isotropic subspaces of GF(2)^2g (masks of a basis each), from
L = {(a, 0)} by transvections x -> x + <x, v> v (they generate Sp(2g, 2),
which is transitive on Lagrangians). prod_{i=1}^g (2^i + 1) of them.
"""
function all_lagrangians(g::Int)
  start = [1 << (i - 1) for i in 1:g]
  seen = Set{Vector{Int}}([_rref_masks(start)])
  queue = [_rref_masks(start)]
  while !isempty(queue)
    B = pop!(queue)
    for v in 1:4^g - 1
      C = [_symplectic_pairing_mask(x, v, g) ? xor(x, v) : x for x in B]
      key = _rref_masks(C)
      key in seen && continue
      push!(seen, key)
      push!(queue, key)
    end
  end
  result = sort!(collect(seen))
  @assert length(result) == prod(2^i + 1 for i in 1:g)
  return result
end

# reduced row echelon form of a list of bit masks (canonical basis of the span)
function _rref_masks(B::Vector{Int})
  rows = copy(B)
  out = Int[]
  while true
    filter!(!iszero, rows)
    isempty(rows) && break
    r = maximum(rows)
    hb = 63 - leading_zeros(r)
    rows = [isodd(x >> hb) ? xor(x, r) : x for x in rows if x != r]
    out = [isodd(x >> hb) ? xor(x, r) : x for x in out]
    push!(out, r)
  end
  return sort!(out)
end

# --- the tables of the neighbour kernel -----------------------------------------

struct NeighbourTables
  g::Int
  lagrangians::Vector{Vector{Int}}
  source::Matrix{Int32}     # source[c + 1, j]: the mask m with M_j . m = (c; 0)
  phase::Matrix{UInt8}      # 8th root of unity (including the reduction sign) for that m
  even::Vector{Int}         # masks of the even characteristics
end

function NeighbourTables(g::Int; lagrangians = all_lagrangians(g), verbose::Bool = true)
  n = length(lagrangians)
  source = zeros(Int32, 2^g, n)
  phase = zeros(UInt8, 2^g, n)
  t = time()
  for (j, B) in enumerate(lagrangians)
    G = [collect(_tuple(x, g)) for x in B]
    M = kernel_to_standard(G, g)
    for m in 0:4^g - 1
      image, phi8 = RSM._igusa_action(M, collect(_tuple(m, g)), g)
      im = _mask(RSM._f2(image))
      im >> g == 0 || continue                     # only the images (c; 0)
      s = RSM._reduction_sign(image, g)
      source[im + 1, j] = m
      phase[im + 1, j] = mod(phi8 + (s == 1 ? 0 : 4), 8)
    end
    verbose && j % 10000 == 0 && (println("  tables: $j of $n ($(round(time() - t, digits = 1)) s)"); flush(stdout))
  end
  even = [m for m in 0:4^g - 1 if RSM._is_even(_tuple(m, g))]
  return NeighbourTables(g, lagrangians, source, phase, even)
end

# in-place Walsh-Hadamard transform: w[b] = sum_c (-1)^(b.c) u[c]
function _walsh_hadamard!(u::Vector)
  n = length(u)
  h = 1
  while h < n
    for i in 0:2h:n - 1, j in i:i + h - 1
      x, y = u[j + 1], u[j + h + 1]
      u[j + 1] = x + y
      u[j + h + 1] = x - y
    end
    h *= 2
  end
  return u
end

@doc raw"""
    neighbour_squares(T, theta, j, zeta_powers) -> Vector

theta_A^2 (vector indexed by masks) of A / G_j from the signed theta
constants `theta` (vector) of A.
"""
function neighbour_squares(T::NeighbourTables, theta::Vector, j::Int, zeta_powers::Vector)
  g = T.g
  n = 2^g
  tvals = [zeta_powers[T.phase[c, j] + 1] * theta[T.source[c, j] + 1] for c in 1:n]
  K = parent(theta[1])
  result = Vector{elem_type(K)}(undef, 4^g)
  u = Vector{elem_type(K)}(undef, n)
  for a in 0:n - 1
    for c in 0:n - 1
      u[c + 1] = tvals[c + 1] * tvals[xor(c, a) + 1]
    end
    _walsh_hadamard!(u)
    for b in 0:n - 1
      result[a | (b << g) + 1] = u[b + 1]
    end
  end
  return result
end

_coeffs(x, d) = ntuple(i -> Int(lift(ZZ, coeff(x, i - 1))), d)

# The theta^8 vector up to scale. On superspecial points the theta^8 take few
# distinct values (e.g. c times the 15th roots of unity for p = 11), so the
# scale must not be fixed by a power v^j (that forgets the arrangement of the
# values): lambda = a Bezout combination of nonzero power sums of weights k
# with gcd 1 -- both I_k = sum over all even characteristics (with
# multiplicities, which can vanish in characteristic p) and P_k = sum over
# the distinct values. Returns v^w / lambda (w the gcd of the weights found,
# almost always 1), w and the number of vanishing theta constants.
function _normalized_eights(T::NeighbourTables, squares::Vector; kmax::Int = 30, coefficients::Bool = false)
  eights = [squares[m + 1]^4 for m in T.even]
  K = parent(eights[1])
  d = degree(K)
  p = Int(characteristic(K))
  zeros_count = count(iszero, eights)
  zeros_count == length(eights) && return nothing, 0, zeros_count
  # coefficients of the theta^8 (extracted once; the distinct values from them)
  C0 = Matrix{Int}(undef, d, length(eights))
  for (j, x) in enumerate(eights), i in 1:d
    C0[i, j] = Int(lift(ZZ, coeff(x, i - 1)))
  end
  seen = Set{Vector{Int}}()
  distinct = elem_type(K)[]
  for (j, x) in enumerate(eights)
    iszero(x) && continue
    c = C0[:, j]
    c in seen && continue
    push!(seen, c)
    push!(distinct, x)
  end
  w, lambda = 0, one(K)
  function add!(k, P)
    iszero(P) && return
    if w == 0
      w, lambda = k, P
    else
      h, x, y = gcdx(w, k)
      h == w && return
      lambda = (x >= 0 ? lambda^x : inv(lambda)^(-x)) * (y >= 0 ? P^y : inv(P)^(-y))
      w = h
    end
  end
  pe, pd = copy(eights), copy(distinct)
  for k in 1:kmax
    if k > 1
      pe .*= eights
      pd .*= distinct
    end
    add!(k, sum(pe))
    w == 1 && break
    add!(k, sum(pd))
    w == 1 && break
  end
  w == 0 && return nothing, 0, zeros_count
  lambda_inv = inv(lambda)
  coefficients || return [x^w * lambda_inv for x in eights], w, zeros_count
  if w == 1
    # multiplication by lambda_inv is linear on the coefficient vectors
    z = gen(K)
    M = Matrix{Int}(undef, d, d)
    for i in 1:d
      y = lambda_inv * z^(i - 1)
      for r in 1:d
        M[r, i] = Int(lift(ZZ, coeff(y, r - 1)))
      end
    end
    return mod.(M * C0, p), w, zeros_count
  end
  v = [x^w * lambda_inv for x in eights]
  C = Matrix{Int}(undef, d, length(v))
  for (j, x) in enumerate(v), i in 1:d
    C[i, j] = Int(lift(ZZ, coeff(x, i - 1)))
  end
  return C, w, zeros_count
end

# Frobenius x -> x^(p^k) on coefficient vectors (basis z^0..z^(d-1)), k = 0..d-1
const _frobenius_cache = Dict{UInt, Vector{Matrix{Int}}}()
function _frobenius_matrices(K)
  get!(_frobenius_cache, objectid(K)) do
    d = degree(K); p = Int(characteristic(K)); z = gen(K)
    [reduce(hcat, [collect(_coeffs(z^(i * big(p)^k), d)) for i in 0:d - 1]) for k in 0:d - 1]
  end
end

# hash of the multiset of the columns of Y (type stable in d)
function _hash_columns(Y::Matrix{Int}, ::Val{d}) where d
  cols = [ntuple(i -> Y[i, j], Val(d)) for j in 1:size(Y, 2)]
  return hash(sort!(cols))
end

@doc raw"""
    frobenius_hashes(T, squares) -> Vector{UInt}, w, zeros

The hashes of the normalized theta^8 multisets (see _normalized_eights) of
the point and of its Frobenius conjugates x -> x^(p^k), k = 0..d-1.
"""
function frobenius_hashes(T::NeighbourTables, squares::Vector)
  C, w, z = _normalized_eights(T, squares; coefficients = true)
  C === nothing && return UInt[], 0, z
  K = parent(squares[1]); d = degree(K); p = Int(characteristic(K))
  hashes = [_hash_columns(mod.(F * C, p), Val(d)) for F in _frobenius_matrices(K)]
  return hashes, w, z
end

# The key of a class: the multiset of the theta^8 = (theta^2)^4 of the even
# characteristics up to a common scalar (Sp(2g, Z) permutes them up to a common
# factor), normalized by _normalized_eights, hashed, minimized over the
# Frobenius conjugates. So classes are Frobenius orbits of isomorphism classes
# over F_p-bar: the theta^8 do not separate a class from its conjugate in
# general (g = 4, p = 11: two conjugate classes with Sp-equivalent theta^8).
function key_from_squares(T::NeighbourTables, squares::Vector)
  h, w, z = frobenius_hashes(T, squares)
  isempty(h) && return "no scale $z"
  return string(w) * "|" * string(z) * "|" * string(minimum(h); base = 16)
end

# the symplectic Fourier transform sum_y (-1)^<x, y> F(y) (masks: x = (a, b))
function _symplectic_transform(F::Vector, g::Int)
  W = _walsh_hadamard!(copy(F))
  low = (1 << g) - 1
  return [W[((x & low) << g | (x >> g)) + 1] for x in 0:4^g - 1]
end

@doc raw"""
    refined_key(T, squares) -> String

A finer invariant than key_from_squares: v = theta^8 (normalized as there,
odd characteristics 0) is permuted by Sp(2g, Z) affinely; the functions
R(x) = sum_m v_m v_(m+x), vhat(x)^2 (vhat the symplectic transform of v) and
the symplectic transforms of R^2 and vhat^4 are permuted by the linear action
x -> M x simultaneously, so the multiset of the tuples
(R(x), vhat(x)^2, (R^2)^(x), (vhat^4)^(x)) over x is an invariant.
"""
function refined_key(T::NeighbourTables, squares::Vector)
  g = T.g
  normalized, w, z = _normalized_eights(T, squares)
  normalized === nothing && return "no scale $z"
  K = parent(normalized[1])
  d = degree(K)
  v = zeros(K, 4^g)
  for (i, m) in enumerate(T.even)
    v[m + 1] = normalized[i]
  end
  vhat2 = [x^2 for x in _symplectic_transform(v, g)]
  R = [sum(v[m + 1] * v[xor(m, x) + 1] for m in T.even) for x in 0:4^g - 1]
  t3 = _symplectic_transform([x^2 for x in R], g)
  t4 = _symplectic_transform([x^2 for x in vhat2], g)
  p = Int(characteristic(K))
  c(x) = collect(_coeffs(x, d))
  rows = [(c(R[i]), c(vhat2[i]), c(t3[i]), c(t4[i])) for i in 1:4^g]
  h = minimum(hash(sort!([Tuple(Tuple(mod.(F * x, p)) for x in r) for r in rows])) for F in _frobenius_matrices(K))
  return "R" * string(w) * "|" * string(h; base = 16)
end

# --- the breadth-first search ---------------------------------------------------
#
# Classes are identified by key_from_squares. That key is not a complete
# invariant (two classes with the same multiset of theta^8 occur, e.g. at
# g = 4, p = 11). Such collisions show up as violations of
# N(A -> B) #Aut(B) = N(B -> A) #Aut(A) (or edges A -> B without B -> A). Then
# the key is marked ambiguous: neighbours with that key are identified by
# refined_key as well, and the classes adjacent to it are expanded again.
# The final certificate: all classes expanded, all relations consistent and
# sum 1/#Aut = the mass formula.

mutable struct ClassRecord
  key::String
  refined::String                    # refined_key ("" until needed)
  parent::Int               # index of the parent class (0 for the start)
  lagrangian::Int           # index j of the Lagrangian from the parent
  vanishing::Int
  thetas::Union{Nothing, Vector}     # signed theta constants (vector), when computed
  signs::Tuple{Int, Int}             # rank, needed (of the Riemann sign system)
  back_check::Bool                   # the dual isogeny leads back to the parent
  expanded::Bool
  adjacency::Dict{Int, Int}          # class => number of Lagrangians leading there
  status::Symbol
  curve::Any                         # quadrics / hyperelliptic polynomial of a Jacobian
  orbit::Int                         # size of the Frobenius orbit (from the neighbours; 0 until expanded)
end

mutable struct BFSState
  p::Int
  g::Int
  field::GluingField
  tables::NeighbourTables
  zeta_powers::Vector
  classes::Vector{ClassRecord}
  index::Dict{String, Vector{Int}}
  ambiguous::Set{String}
  start_aut::Int                      # #Aut of the start E^g (product polarization)
  dual::Int                           # index of the Lagrangian {(0, b)}
end

# #Aut(E) of y^2 = x (x - 1) (x - lambda), p >= 5
function _elliptic_aut_order(lambda)
  j = 256 * (lambda^2 - lambda + 1)^3 / (lambda^2 * (lambda - 1)^2)
  return j == 1728 ? 4 : iszero(j) ? 6 : 2
end

function BFSState(p::Int, g::Int; k::Int = 8, tables = nothing, lambda = nothing)
  F = GluingField(p, k)
  T = tables === nothing ? NeighbourTables(g) : tables
  lambda === nothing && (lambda = supersingular_lambdas(F.L)[1])
  thetas = theta_vector(product_thetas([legendre_thetas(F, lambda) for _ in 1:g]), g)
  zp = [F.zeta8^i for i in 0:7]
  key = key_from_squares(T, [x^2 for x in thetas])
  start = ClassRecord(key, "", 0, 0, count(m -> iszero(thetas[m + 1]), T.even), thetas, (0, 0), true, false,
                      Dict{Int, Int}(), :product, nothing, 0)
  # Aut(E^g, product polarization) = monomial matrices over Aut(E)
  aut = _elliptic_aut_order(lambda)^g * factorial(g)
  dual = findfirst(==(_rref_masks([1 << (g + i - 1) for i in 1:g])), T.lagrangians)
  return BFSState(p, g, F, T, zp, [start], Dict(key => [1]), Set{String}(), aut, dual)
end

# theta^2 of class i: from its thetas, or recomputed from its parent (cheaper
# than storing them for all classes not expanded yet)
function _class_squares(state::BFSState, i::Int)
  rec = state.classes[i]
  rec.thetas === nothing || return [x^2 for x in rec.thetas]
  return neighbour_squares(state.tables, state.classes[rec.parent].thetas, rec.lagrangian, state.zeta_powers)
end

function _refined!(state::BFSState, i::Int)
  rec = state.classes[i]
  isempty(rec.refined) && (rec.refined = refined_key(state.tables, _class_squares(state, i)))
  return rec.refined
end

# The class of a point given by its theta^2 (0 if new)
# The class with this key (and refined key rk, if the key is ambiguous); 0 if new
function _lookup(state::BFSState, key::String, rk::String)
  candidates = get(state.index, key, Int[])
  isempty(candidates) && return 0
  key in state.ambiguous || return candidates[1]
  for c in candidates
    _refined!(state, c) == rk && return c
  end
  return 0
end

function _new_class!(state::BFSState, key::String, rk::String, vanishing::Int, parent::Int, j::Int)
  push!(state.classes, ClassRecord(key, rk, parent, j, vanishing, nothing, (0, 0), false, false,
                                   Dict{Int, Int}(), :untested, nothing, 0))
  i = length(state.classes)
  push!(get!(state.index, key, Int[]), i)
  return i
end

# does the dual isogeny of the (signed) point v lead back to the parent?
function _back_to_parent(state::BFSState, v::Vector, parent::Int)
  sq = neighbour_squares(state.tables, v, state.dual, state.zeta_powers)
  key = key_from_squares(state.tables, sq)
  key == state.classes[parent].key || return false
  key in state.ambiguous || return true
  return refined_key(state.tables, sq) == _refined!(state, parent)
end

# Signed theta constants of class i from its squares: square roots, signs by
# Riemann's relations; the remaining signs (solutions of the homogeneous
# system, at most 2^max_free choices) chosen by the dual isogeny, which must
# lead back to the parent
function signed_thetas!(state::BFSState, i::Int; max_free::Int = 8)
  rec = state.classes[i]
  rec.thetas === nothing || return rec.thetas
  g = state.g
  squares = _class_squares(state, i)
  thetas = theta_dict([iszero(x) ? x : _sqrt_exact(x) for x in squares], g)
  pairs = g >= 4 ? RSM.load_sign_data(RSM._default_sign_data_file(g)) : Any[]
  _, rank, needed, _, S, non_fixed = correct_signs_exact3!(thetas, g; pairs = pairs)
  rec.signs = (rank, needed)
  v = theta_vector(thetas, g)
  ok = _back_to_parent(state, v, rec.parent)
  if !ok && rank < needed
    nulls = sign_null_vectors(S, non_fixed)
    nf = min(length(nulls), max_free)
    for mask in 1:2^nf - 1
      w = copy(v)
      for b in 1:nf
        isodd(mask >> (b - 1)) || continue
        for c in nulls[b]
          w[_mask(c) + 1] = -w[_mask(c) + 1]
        end
      end
      if _back_to_parent(state, w, rec.parent)
        v, ok = w, true
        break
      end
    end
  end
  rec.back_check = ok
  rec.thetas = v
  return v
end

# --- the neighbours of one class, serial or on worker processes ------------------
#
# Threads are not used: Nemo's finite field arithmetic crashed (segmentation
# fault in fq_nmod_reduce) with several threads. Worker processes (julia -p N)
# each hold the tables and the field; per class they get the signed theta
# constants (as coefficients) and a range of Lagrangians.

using Distributed

# per Lagrangian j: the key, the refined key (ambiguous keys only), the number
# of vanishing even theta constants, the Frobenius conjugate hashes
function _neighbour_chunk(T::NeighbourTables, thetas::Vector, zeta_powers::Vector, js, ambiguous)
  out = Vector{Tuple{String, String, Int, Vector{UInt}}}(undef, length(js))
  for (k, j) in enumerate(js)
    squares = neighbour_squares(T, thetas, j, zeta_powers)
    h, w, z = frobenius_hashes(T, squares)
    key = isempty(h) ? "no scale $z" : string(w) * "|" * string(z) * "|" * string(minimum(h); base = 16)
    rk = key in ambiguous ? refined_key(T, squares) : ""
    out[k] = (key, rk, count(m -> iszero(squares[m + 1]), T.even), h)
  end
  return out
end

# worker side
const _WORKER = Dict{Symbol, Any}()

function _worker_setup(tables_file::String, p::Int, k::Int, zeta8::Matrix{UInt16})
  F0 = GluingField(p, k)
  K = F0.L
  zeta = _decode(zeta8, K)[1]
  _WORKER[:tables] = open(Serialization.deserialize, tables_file)
  _WORKER[:field] = K
  _WORKER[:zeta_powers] = [zeta^i for i in 0:7]
  return nothing
end

function _worker_chunk(theta_coefficients::Matrix{UInt16}, js::UnitRange{Int}, ambiguous::Set{String})
  thetas = _decode(theta_coefficients, _WORKER[:field])
  return _neighbour_chunk(_WORKER[:tables], thetas, _WORKER[:zeta_powers], js, ambiguous)
end

const _WORKERS_READY = Ref(false)

@doc raw"""
    setup_workers(state, tables_file)

Loads the tables (serialized NeighbourTables, see run_bfs.jl) and the field
on all worker processes. The workers must have loaded this file
(@everywhere include("superspecial_bfs.jl")).
"""
function setup_workers(state::BFSState, tables_file::AbstractString)
  d = degree(state.field.L)
  z8 = _encode([state.field.zeta8], d)
  @sync for w in workers()
    @async remotecall_wait(_worker_setup, w, String(tables_file), state.p, d, z8)
  end
  _WORKERS_READY[] = true
  return nothing
end

function _neighbour_data(state::BFSState, thetas::Vector)
  T = state.tables
  n = length(T.lagrangians)
  if nworkers() > 1 || (nprocs() > 1 && _WORKERS_READY[])
    @assert _WORKERS_READY[] "call setup_workers first"
    d = degree(state.field.L)
    enc = _encode(thetas, d)
    chunks = [r for r in Iterators.partition(1:n, cld(n, 8 * nworkers()))]
    amb = copy(state.ambiguous)
    results = pmap(js -> _worker_chunk(enc, js, amb), chunks)
    data = reduce(vcat, results)
  else
    data = _neighbour_chunk(T, thetas, state.zeta_powers, 1:n, state.ambiguous)
  end
  return [x[1] for x in data], [x[2] for x in data], [x[3] for x in data], [x[4] for x in data]
end

@doc raw"""
    expand!(state, i) -> number of new classes

All neighbours of class i (signed theta constants computed first): their
classes and the adjacency counts. The neighbours are computed by the worker
processes if there are any (julia -p N, see _neighbour_data); the classes
are then assigned in order. Also used to
expand a class again after a key became ambiguous.
"""
function expand!(state::BFSState, i::Int; verbose::Bool = true)
  rec = state.classes[i]
  t = time()
  thetas = signed_thetas!(state, i)
  t_signs = time() - t
  T = state.tables
  n = length(T.lagrangians)
  d = degree(state.field.L)
  for k in state.ambiguous, c in state.index[k]  # refined keys of the existing classes
    _refined!(state, c)
  end
  keys_j, refined_j, vanishing_j, hashes_j = _neighbour_data(state, thetas)
  t_neighbours = time() - t - t_signs
  new = 0
  adjacency = Dict{Int, Int}()
  for j in 1:n
    target = _lookup(state, keys_j[j], refined_j[j])
    if target == 0
      target = _new_class!(state, keys_j[j], refined_j[j], vanishing_j[j], i, j)
      new += 1
    end
    adjacency[target] = get(adjacency, target, 0) + 1
  end
  again = rec.expanded
  # the Frobenius orbit of the class: the conjugates of its neighbour multiset
  conjugate_keys = [sort!([h[k] for h in hashes_j if length(h) >= k]) for k in 1:d]
  rec.orbit = length(unique([hash(c) for c in conjugate_keys if !isempty(c)]))
  rec.adjacency = adjacency
  rec.expanded = true
  verbose && println("$(again ? "re-" : "")expanded class $i (vanishing $(rec.vanishing), signs $(rec.signs[1])/$(rec.signs[2]), " *
                     "back check $(rec.back_check), Frobenius orbit $(rec.orbit)): $new new, $(length(state.classes)) classes, " *
                     "$(length(adjacency)) distinct neighbours, $(round(time() - t, digits = 1)) s " *
                     "(signs $(round(t_signs, digits = 1)) s, neighbours $(round(t_neighbours, digits = 1)) s, $(nworkers()) workers)")
  flush(stdout)
  return new
end

# The Jacobian test of an expanded class (test_vertex! of superspecial.jl)
function test_class!(state::BFSState, i::Int)
  rec = state.classes[i]
  rec.status == :untested || return rec.status
  g = state.g
  dummy = SuperspecialSearch(state.p, g, state.field, Dict{String, Vertex}(), String[], "", 0, String[],
                             Random.MersenneTwister(1))
  v = Vertex(rec.key, theta_dict(rec.thetas, g), rec.vanishing, rec.signs[1] == rec.signs[2], :untested, nothing)
  try
    test_vertex!(dummy, v)
  catch err
    v.status = :test_error
    println("  test error at class $i: ", first(sprint(showerror, err), 200))
  end
  rec.status = v.status
  rec.curve = v.quadrics
  return rec.status
end

@doc raw"""
    automorphism_orders(state) -> Vector, Bool, Vector{Tuple{Int, Int}}

#Aut of every class from #Aut of the start and the adjacency counts:
N(A -> B) #Aut(B) = N(B -> A) #Aut(A) (isogenies A -> B with Lagrangian
kernel and their duals). Returns the orders, whether all relations hold, and
the edges where they do not.
"""
function automorphism_orders(state::BFSState)
  n = length(state.classes)
  aut = Vector{Union{Nothing, Rational{BigInt}}}(nothing, n)
  aut[1] = state.start_aut // max(state.classes[1].orbit, 1)   # Aut* of the start
  queue = [1]
  while !isempty(queue)
    a = popfirst!(queue)
    ra = state.classes[a]
    ra.expanded || continue
    for (b, nab) in ra.adjacency
      rb = state.classes[b]
      (rb.expanded && aut[b] === nothing) || continue
      nba = get(rb.adjacency, a, 0)
      nba == 0 && continue
      aut[b] = aut[a] * nba // nab
      push!(queue, b)
    end
  end
  bad = Tuple{Int, Int}[]
  for (a, ra) in enumerate(state.classes)
    ra.expanded || continue
    for (b, nab) in ra.adjacency
      state.classes[b].expanded || continue
      nba = get(state.classes[b].adjacency, a, 0)
      if nba == 0 || aut[a] === nothing || aut[b] === nothing || aut[a] * nba != aut[b] * nab
        push!(bad, (a, b))
      end
    end
  end
  return aut, isempty(bad), bad
end

# Marks the keys of suspicious classes ambiguous and expands their
# neighbours again; returns the number of keys marked
function split_collisions!(state::BFSState; verbose::Bool = true)
  _, consistent, bad = automorphism_orders(state)
  consistent && return 0
  # an edge a -> b without b -> a: b's key collides; otherwise both ends
  suspicious = Set{Int}()
  for (a, b) in bad
    get(state.classes[b].adjacency, a, 0) == 0 && push!(suspicious, b)
  end
  isempty(suspicious) && for (a, b) in bad
    push!(suspicious, a); push!(suspicious, b)
  end
  keys_new = setdiff(Set(state.classes[i].key for i in suspicious), state.ambiguous)
  isempty(keys_new) && return 0
  union!(state.ambiguous, keys_new)
  members = Set(i for k in keys_new for i in state.index[k])
  for i in members
    _refined!(state, i)
  end
  # classes with the same key and the same refined key cannot be split
  for k in keys_new
    rks = [state.classes[i].refined for i in state.index[k]]
    allunique(rks) || println("WARNING: classes $(state.index[k]) share key and refined key")
  end
  redo = sort!(collect(Set(a for (a, ra) in enumerate(state.classes) if ra.expanded && any(b -> b in members, keys(ra.adjacency)))))
  verbose && println("ambiguous keys: $(length(keys_new)) (classes $(sort!(collect(members)))); expanding $(length(redo)) classes again")
  for a in redo
    expand!(state, a; verbose = verbose)
  end
  return length(keys_new)
end

@doc raw"""
    bfs!(state; max_expansions, test = true, checkpoint = nothing)

Expands (and tests) classes in order of discovery until all are expanded
(the closure: every neighbour of every class is known, so by connectedness
all classes are found) or `max_expansions` are done; then splits colliding
keys and continues, until the closure is consistent.
"""
function bfs!(state::BFSState; max_expansions::Int = typemax(Int), test::Bool = true,
              checkpoint = nothing, verbose::Bool = true, max_rounds::Int = 20,
              state_file = nothing, state_interval::Real = 600)
  done = 0
  last_save = time()
  for _round in 1:max_rounds
    i = 1
    while i <= length(state.classes) && done < max_expansions
      if !state.classes[i].expanded
        expand!(state, i; verbose = verbose)
        if test && state.classes[i].status == :untested
          t = time()
          s = test_class!(state, i)
          verbose && println("  class $i: $s ($(round(time() - t, digits = 1)) s)")
          s == :jacobian && println("  *** JACOBIAN: class $i ***")
        end
        done += 1
        checkpoint === nothing || save_bfs(state, checkpoint)
        if state_file !== nothing && time() - last_save > state_interval
          save_state(state, state_file)
          last_save = time()
        end
      end
      i += 1
    end
    all(r -> r.expanded, state.classes) || break
    split_collisions!(state; verbose = verbose) == 0 && break
  end
  complete = all(r -> r.expanded, state.classes)
  verbose && println(complete ? "CLOSED: $(length(state.classes)) classes, all neighbours known" :
                                "$(count(r -> r.expanded, state.classes)) of $(length(state.classes)) classes expanded")
  checkpoint === nothing || save_bfs(state, checkpoint)
  state_file === nothing || save_state(state, state_file)
  return complete
end

function mass_check(state::BFSState; verbose::Bool = true)
  aut, consistent, bad = automorphism_orders(state)
  known = [a for a in aut if a !== nothing]
  total = sum(1 // a for a in known)
  expected = mass(state.g, state.p)
  integral = all(a -> isone(denominator(a)), known)
  orbits = sum(r.orbit for r in state.classes)
  verbose && println("Frobenius orbits $(length(state.classes)) (classes over F_p-bar, from the neighbour multisets: $orbits); #Aut* = #Aut / orbit size known for $(length(known)); consistent: $consistent ($(length(bad)) bad edges); " *
                     "#Aut* integral: $integral; sum 1/#Aut = $total, mass formula = $expected; equal: $(total == expected)")
  return (aut = aut, consistent = consistent, total = total, expected = expected, complete = total == expected)
end

function save_bfs(state::BFSState, path::AbstractString)
  aut, consistent, _ = automorphism_orders(state)
  tmp = path * ".tmp"
  open(tmp, "w") do io
    println(io, "# p = $(state.p), g = $(state.g), classes = $(length(state.classes)), expanded = $(count(r -> r.expanded, state.classes)), consistent = $consistent")
    println(io, "# index\tparent\tlagrangian\tvanishing\tsigns\tback_check\texpanded\tdistinct_neighbours\taut_star\torbit\tstatus\tkey\trefined")
    for (i, r) in enumerate(state.classes)
      println(io, join((i, r.parent, r.lagrangian, r.vanishing, "$(r.signs[1])/$(r.signs[2])", r.back_check,
                        r.expanded, length(r.adjacency), aut[i] === nothing ? "?" : string(aut[i]), r.orbit, r.status, r.key, r.refined), "\t"))
    end
  end
  mv(tmp, path; force = true)
  open(path * ".jacobians", "w") do io
    for (i, r) in enumerate(state.classes)
      r.status == :jacobian || continue
      println(io, "# class $i")
      println(io, r.curve isa Vector ? export_forms(r.curve) : string(r.curve))
    end
  end
end

# --- checkpoints ----------------------------------------------------------------
#
# The state is a text file (Julia's Serialization format depends on the Julia
# version, so it cannot be moved between machines): a header, then one line
# per class with tab separated fields; the signed theta constants as base64
# of their coefficients (one byte each, p < 256).

using Serialization, Base64

_encode(v::Vector, d::Int) = UInt16[Int(lift(ZZ, coeff(x, i - 1))) for i in 1:d, x in v]
_decode(M::Matrix{UInt16}, K) = (z = gen(K); [sum(K(Int(M[i, j])) * z^(i - 1) for i in 1:size(M, 1)) for j in 1:size(M, 2)])

_pack(M::Matrix{UInt16}) = base64encode(UInt8.(vec(M)))
_unpack(s::AbstractString, d::Int) = (b = base64decode(s); reshape(UInt16.(b), d, length(b) ÷ d))

const _STATE_MAGIC = "# superspecial_bfs state v1"

@doc raw"""
    save_state(state, path)

Everything needed to continue the search (load_state): the classes with
their signed theta constants (when computed), adjacency counts, statuses,
curves (as text) and Frobenius orbits, the ambiguous keys. Written to
path.tmp first.
"""
function save_state(state::BFSState, path::AbstractString)
  K = state.field.L
  d = degree(K)
  @req state.p < 256 "save_state stores coefficients as bytes (p < 256)"
  f = defining_polynomial(K)
  esc(x) = escape_string(string(x))
  open(path * ".tmp", "w") do io
    println(io, _STATE_MAGIC)
    println(io, "p\t", state.p)
    println(io, "g\t", state.g)
    println(io, "k\t", d)
    println(io, "defining\t", join([Int(lift(ZZ, coeff(f, i))) for i in 0:d], ","))
    println(io, "zeta8\t", _pack(_encode([state.field.zeta8], d)))
    println(io, "start_aut\t", state.start_aut)
    println(io, "ambiguous\t", join(esc.(collect(state.ambiguous)), "\t"))
    println(io, "classes\t", length(state.classes))
    for r in state.classes
      curve = r.curve === nothing ? "-" : esc(r.curve isa Vector ? export_forms(r.curve) : r.curve)
      fields = (esc(r.key), isempty(r.refined) ? "-" : esc(r.refined), r.parent, r.lagrangian, r.vanishing,
                r.thetas === nothing ? "-" : _pack(_encode(r.thetas, d)), "$(r.signs[1])/$(r.signs[2])",
                Int(r.back_check), Int(r.expanded), join(["$b:$n" for (b, n) in sort!(collect(r.adjacency))], ","),
                r.status, r.orbit, curve)
      println(io, join(fields, "\t"))
    end
  end
  mv(path * ".tmp", path; force = true)
end

function _read_state(path::AbstractString)
  lines = readlines(path)
  @req !isempty(lines) && lines[1] == _STATE_MAGIC "$path is not a state file of superspecial_bfs.jl"
  header = Dict{String, String}()
  i = 2
  while true
    key, value = split(lines[i], "\t"; limit = 2)
    header[key] = value
    i += 1
    key == "classes" && break
  end
  d = parse(Int, header["k"])
  unesc(x) = unescape_string(x)
  classes = map(lines[i:i + parse(Int, header["classes"]) - 1]) do line
    f = split(line, "\t")
    adjacency = Dict{Int, Int}()
    if !isempty(f[10])
      for e in split(f[10], ",")
        b, n = split(e, ":")
        adjacency[parse(Int, b)] = parse(Int, n)
      end
    end
    s1, s2 = parse.(Int, split(f[7], "/"))
    (key = unesc(f[1]), refined = f[2] == "-" ? "" : unesc(f[2]), parent = parse(Int, f[3]), lagrangian = parse(Int, f[4]),
     vanishing = parse(Int, f[5]), thetas = f[6] == "-" ? nothing : _unpack(f[6], d), signs = (s1, s2),
     back_check = f[8] == "1", expanded = f[9] == "1", adjacency = adjacency, status = Symbol(f[11]),
     orbit = parse(Int, f[12]), curve = f[13] == "-" ? nothing : unesc(f[13]))
  end
  amb = header["ambiguous"]
  return (p = parse(Int, header["p"]), g = parse(Int, header["g"]), k = d,
          defining = parse.(Int, split(header["defining"], ",")), zeta8 = _unpack(header["zeta8"], d),
          start_aut = parse(Int, header["start_aut"]), ambiguous = isempty(amb) ? String[] : unesc.(split(amb, "\t")),
          classes = classes)
end

@doc raw"""
    load_state(path; tables = nothing, rekey = true) -> BFSState

Continues a search saved by save_state (Jacobian curves are kept as their
exported text). Also reads the older serialized states (same Julia version
only). The keys are hashes, which may differ between Julia versions: with
`rekey` they are recomputed (from the theta constants, or from the parent for
classes not expanded yet), so a state can be moved to another machine.
"""
function load_state(path::AbstractString; tables = nothing, rekey::Bool = true, verbose::Bool = true)
  text = open(io -> String(read(io, length(_STATE_MAGIC))), path) == _STATE_MAGIC
  data = text ? _read_state(path) : open(deserialize, path)
  F0 = GluingField(data.p, data.k)
  K = F0.L
  if hasproperty(data, :defining)
    f = defining_polynomial(K)
    @req [Int(lift(ZZ, coeff(f, i))) for i in 0:data.k] == data.defining "The finite field GF($(data.p)^$(data.k)) has another defining polynomial here than in the saved state."
  end
  F = GluingField(K, _decode(data.zeta8, K)[1])
  T = tables === nothing ? NeighbourTables(data.g) : tables
  classes = ClassRecord[]
  for c in data.classes
    push!(classes, ClassRecord(c.key, c.refined, c.parent, c.lagrangian, c.vanishing,
                               c.thetas === nothing ? nothing : _decode(c.thetas, K), c.signs, c.back_check,
                               c.expanded, c.adjacency, c.status, c.curve, c.orbit))
  end
  dual = findfirst(==(_rref_masks([1 << (data.g + i - 1) for i in 1:data.g])), T.lagrangians)
  state = BFSState(data.p, data.g, F, T, [F.zeta8^i for i in 0:7], classes, Dict{String, Vector{Int}}(),
                   Set{String}(data.ambiguous), data.start_aut, dual)
  if rekey
    t = time()
    old_ambiguous = state.ambiguous
    state.ambiguous = Set{String}()
    for (i, r) in enumerate(state.classes)
      old = r.key
      r.key = key_from_squares(T, _class_squares(state, i))
      old in old_ambiguous && push!(state.ambiguous, r.key)
      r.refined = ""
    end
    changed = count(i -> state.classes[i].key != data.classes[i].key, eachindex(state.classes))
    verbose && println("keys recomputed ($(round(time() - t, digits = 1)) s): $changed of $(length(state.classes)) changed")
  end
  for (i, r) in enumerate(state.classes)
    push!(get!(state.index, r.key, Int[]), i)
  end
  for (k, members) in state.index
    length(members) > 1 && !(k in state.ambiguous) && @warn "classes $members share the key $k"
  end
  return state
end

# --- the Jacobian tests in parallel (after the enumeration) -------------------------

function _test_worker_setup(p::Int, k::Int, zeta8::Matrix{UInt16})
  K = GluingField(p, k).L
  _WORKER[:gluing_field] = GluingField(K, _decode(zeta8, K)[1])
  return nothing
end

# the test of one class on a worker: status and the curve (as text)
function _test_worker(g::Int, key::String, vanishing::Int, complete::Bool, theta_coefficients::Matrix{UInt16})
  F = _WORKER[:gluing_field]
  p = Int(characteristic(F.L))
  thetas = _decode(theta_coefficients, F.L)
  dummy = SuperspecialSearch(p, g, F, Dict{String, Vertex}(), String[], "", 0, String[], Random.MersenneTwister(1))
  v = Vertex(key, theta_dict(thetas, g), vanishing, complete, :untested, nothing)
  t = time()
  try
    test_vertex!(dummy, v)
  catch err
    v.status = :test_error
  end
  curve = v.quadrics === nothing ? nothing : v.quadrics isa Vector ? string(export_forms(v.quadrics)) : string(v.quadrics)
  status, elapsed = v.status, time() - t
  v = nothing
  GC.gc()          # the Fay kernels need several GB; give them back before the next class
  return status, curve, elapsed
end

@doc raw"""
    test_classes!(state; classes = all expanded untested classes, checkpoint, state_file)

The Jacobian tests of the classes, on the worker processes if there are any
(pmap, one class per task). Results are stored in the state; the files are
rewritten every `save_every` results.
"""
function test_classes!(state::BFSState; classes = nothing, checkpoint = nothing, state_file = nothing,
                       save_every::Int = 50, verbose::Bool = true)
  todo = classes === nothing ? [i for (i, r) in enumerate(state.classes) if r.expanded && r.status == :untested] : classes
  verbose && println("testing $(length(todo)) classes on $(nworkers()) workers"); flush(stdout)
  d = degree(state.field.L)
  z8 = _encode([state.field.zeta8], d)
  for w in workers()
    remotecall_wait(_test_worker_setup, w, state.p, d, z8)
  end
  nprocs() == 1 && _test_worker_setup(state.p, d, z8)
  g = state.g
  jobs = [(i, state.classes[i].key, state.classes[i].vanishing, state.classes[i].signs[1] == state.classes[i].signs[2],
           _encode(state.classes[i].thetas, d)) for i in todo]
  done = Threads.Atomic{Int}(0)
  lk = ReentrantLock()
  t0 = time()
  # results are stored as they come in (asyncmap keeps nworkers() tasks running)
  asyncmap(jobs; ntasks = max(nworkers(), 1)) do (i, key, van, complete, enc)
    status, curve, t = nprocs() > 1 ? remotecall_fetch(_test_worker, default_worker_pool(), g, key, van, complete, enc) :
                                      _test_worker(g, key, van, complete, enc)
    lock(lk) do
      state.classes[i].status = status
      state.classes[i].curve = curve
      n = (done[] += 1)
      verbose && println("  class $i: $status ($(round(t, digits = 1)) s) [$n of $(length(jobs)), $(round(time() - t0, digits = 0)) s]")
      status == :jacobian && println("  *** JACOBIAN: class $i ***")
      flush(stdout)
      if n % save_every == 0 || status == :jacobian
        checkpoint === nothing || save_bfs(state, checkpoint)
        state_file === nothing || save_state(state, state_file)
      end
    end
  end
  checkpoint === nothing || save_bfs(state, checkpoint)
  state_file === nothing || save_state(state, state_file)
  return count(r -> r.status == :jacobian, state.classes)
end

@doc raw"""
    load_or_build_tables(g, path) -> NeighbourTables

The tables from `path` (Serialization: only readable by the Julia version
that wrote it), else built (about 6 min for g = 5) and saved there.
"""
function load_or_build_tables(g::Int, path::AbstractString; verbose::Bool = true)
  if isfile(path)
    T = try
      open(deserialize, path)
    catch err
      verbose && println("cannot read $path ($(typeof(err))): building the tables again")
      nothing
    end
    T isa NeighbourTables && T.g == g && return T
  end
  t = @elapsed T = NeighbourTables(g; verbose = verbose)
  verbose && println("tables: $(length(T.lagrangians)) Lagrangians, $(round(t, digits = 1)) s")
  open(io -> serialize(io, T), path * ".tmp", "w")
  mv(path * ".tmp", path; force = true)
  return T
end
