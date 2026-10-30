################################################################################
#
#  superspecial.jl : searching superspecial curves of genus g by walking the
#  (2,...,2)-isogeny graph of superspecial principally polarized abelian
#  varieties in theta coordinates (the genus 3 method of Ohashi-Onuki-Kudo-
#  Yoshizumi-Nuida, extended to g >= 4 with the gluing formula and the
#  genus-g reconstruction).
#
#  Vertices: principally polarized superspecial abelian varieties A of
#  dimension g over GF(p)bar, given by a theta null point (all 4^g theta
#  constants with signs, over L = GF(p, k)). Start: E^g, E supersingular in
#  Legendre form. Edges: A -> A / G, G maximal isotropic in A[2]
#  (glue_theta_squares with one piece), then square roots and signs (Riemann's
#  relations). A (2,...,2)-isogeny is prime to p, so every vertex is again
#  superspecial: a vertex that is a Jacobian gives a superspecial curve.
#
#  Isomorphism classes: invariants I_k = sum over even m of theta[m]^(8k)
#  (modular forms of weight 4k for Sp(2g, Z)), compared as a point of weighted
#  projective space.
#
#  Usage (Hecke checkout with src/RieSrf; gluing_prototype.jl next to this file):
#     include("superspecial.jl")
#     state = SuperspecialSearch(7, 5; k = 16)          # p, g
#     random_walk!(state, 200)                           # steps
#     summary(state)
#
################################################################################

include(joinpath(@__DIR__, "gluing_prototype.jl"))

################################################################################
#  Supersingular elliptic curves in Legendre form
################################################################################

# The Legendre lambda of the supersingular elliptic curves in characteristic p:
# the roots of the Hasse polynomial sum_i binomial((p-1)/2, i)^2 lambda^i
function supersingular_lambdas(L::FqField)
  p = Int(characteristic(L))
  m = div(p - 1, 2)
  Lx, x = polynomial_ring(L, :x; cached = false)
  H = sum(L(binomial(m, i)^2) * x^i for i in 0:m)
  return roots(H)
end

################################################################################
#  Isomorphism invariants
################################################################################

# I_k = sum over even characteristics of theta[m]^(8k), k = 1..n
function theta_power_sums(thetas, g::Int; n::Int = 8)
  K = parent(first(values(thetas)))
  eights = [thetas[c]^8 for c in RSM.even_theta_characteristics(g)]
  return [sum(e^k for e in eights) for k in 1:n]
end

# A key for the point (I_1 : ... : I_n) of weighted projective space (weights
# 1..n): with j0 the first index with I_j0 != 0, the values I_j^j0 / I_j0^j
function isomorphism_key(thetas, g::Int; n::Int = 8)
  I = theta_power_sums(thetas, g; n = n)
  j0 = findfirst(!iszero, I)
  j0 === nothing && return "all zero"
  return join([string(j0); [string(divexact(I[j]^j0, I[j0]^j)) for j in 1:n]], "|")
end

################################################################################
#  The search state
################################################################################

mutable struct Vertex
  key::String
  thetas::Dict
  vanishing::Int          # even theta constants that vanish
  signs_complete::Bool    # all signs determined by Riemann's relations
  status::Symbol          # :untested, :jacobian, :not_jacobian, :decomposable?, ...
  quadrics::Any
end

mutable struct SuperspecialSearch
  p::Int
  g::Int
  field::GluingField
  vertices::Dict{String, Vertex}
  order::Vector{String}            # in order of discovery
  current::String
  steps::Int
  log::Vector{String}
  rng::Random.AbstractRNG
end

function _vertex(F::GluingField, thetas, g::Int)
  vanishing = count(c -> RSM._is_even(c) && iszero(thetas[c]), keys(thetas))
  return Vertex(isomorphism_key(thetas, g), thetas, vanishing, true, :untested, nothing)
end

@doc raw"""
    SuperspecialSearch(p, g; k = 16, seed = 1, lambdas = nothing) -> state

The start of the search: E_1 x ... x E_g with E_i supersingular (Legendre
form, lambda_i among the roots of the Hasse polynomial; by default all
equal), theta constants over GF(p^k).
"""
function SuperspecialSearch(p::Int, g::Int; k::Int = 16, seed::Int = 1, lambdas = nothing)
  F = GluingField(p, k)
  ss = supersingular_lambdas(F.L)
  @req !isempty(ss) "No supersingular lambda in GF($p^$k)."
  lambdas === nothing && (lambdas = fill(ss[1], g))
  pieces = [legendre_thetas(F, l) for l in lambdas]
  thetas = product_thetas(pieces)
  v = _vertex(F, thetas, g)
  state = SuperspecialSearch(p, g, F, Dict(v.key => v), [v.key], v.key, 0, String[], Random.MersenneTwister(seed))
  v.status = :product
  return state
end

################################################################################
#  One isogeny step
################################################################################

@doc raw"""
    isogenous_thetas(F, thetas, G) -> thetas_new, rank, needed

The theta null point of A / G (G maximal isotropic in A[2], characteristic
coordinates) with signs from Riemann's relations.
"""
function isogenous_thetas(F::GluingField, thetas, G; max_tries::Int = 3000)
  g = length(G)
  squares, _ = glue_theta_squares([thetas], G, F.zeta8)
  new = theta_from_squares(squares)
  _, rank, needed = correct_signs_exact!(new, g; max_tries = max_tries)
  return new, rank, needed
end

# Square roots, signs, the vertex (stored and tested if new); returns the
# stored vertex of its class
function _add_vertex!(state::SuperspecialSearch, squares; test::Bool = true, sign_tries::Int = 3000,
                      verbose::Bool = true)
  g = state.g
  thetas = theta_from_squares(squares)
  local res
  t_signs = @elapsed (res = correct_signs_exact!(thetas, g; max_tries = sign_tries))
  rank, needed = res[2], res[3]
  v = _vertex(state.field, thetas, g)
  v.signs_complete = rank == needed
  haskey(state.vertices, v.key) && return state.vertices[v.key], false
  state.vertices[v.key] = v
  push!(state.order, v.key)
  t_test = test ? (@elapsed test_vertex!(state, v)) : 0.0
  verbose && println("step $(state.steps): new class #$(length(state.order)), vanishing $(v.vanishing), " *
                     "signs $(rank)/$(needed), status $(v.status)  [signs $(round(t_signs, digits=1)) s, test $(round(t_test, digits=1)) s]")
  v.status == :jacobian && println("  *** JACOBIAN: superspecial curve of genus $g in characteristic $(state.p) ***")
  flush(stdout)
  return v, true
end

@doc raw"""
    random_walk!(state, steps; test = true, special_rate = 0.05, max_vanishing = 100,
                 candidates = 200, sign_tries = 3000, verbose = true)

`steps` steps of a random walk in the (2,...,2)-isogeny graph. In each step
random Lagrangians G are tried (only theta_A^2, cheap) until A / G has no
vanishing even theta constant; the walk moves there (square roots, signs from
Riemann's relations, stored and tested if new). Neighbours with vanishing
theta constants (special abelian varieties: their signs are often not all
determined, so the walk does not continue from them) are processed as leaves
with probability `special_rate` (and at most `max_vanishing` vanishing
theta constants). If no generic neighbour is found among `candidates`, the walk
restarts from a random earlier vertex with complete signs.
"""
function random_walk!(state::SuperspecialSearch, steps::Int; test::Bool = true, special_rate::Float64 = 0.05,
                      max_vanishing::Int = 100, candidates::Int = 200, sign_tries::Int = 3000,
                      verbose::Bool = true)
  g = state.g
  for _ in 1:steps
    state.steps += 1
    current = state.vertices[state.current]
    moved = false
    for _ in 1:candidates
      G = random_lagrangian(g; rng = state.rng)
      squares, _ = glue_theta_squares([current.thetas], G, state.field.zeta8)
      vanishing = count(c -> RSM._is_even(c) && iszero(squares[c]), keys(squares))
      try
        if vanishing == 0
          v, _ = _add_vertex!(state, squares; test = test, sign_tries = sign_tries, verbose = verbose)
          if v.signs_complete
            state.current = v.key
            moved = true
            break
          end
        elseif vanishing <= max_vanishing && rand(state.rng) < special_rate
          _add_vertex!(state, squares; test = test, sign_tries = sign_tries, verbose = verbose)
        end
      catch err
        err isa NeedExtension || rethrow()
        push!(state.log, "step $(state.steps): square root missing (increase k)")
      end
    end
    if !moved
      good = [k for k in state.order if state.vertices[k].signs_complete]
      state.current = good[rand(state.rng, 1:length(good))]
    end
  end
  return state
end

@doc raw"""
    test_vertex!(state, v; tries = 8)

Whether the vertex is a Jacobian: the exact genus-g reconstruction (other
eta by random symplectic changes of basis if the first is degenerate).
Products (theta constants of a product vanish at odd x odd
characteristics) are not tested.
"""
function test_vertex!(state::SuperspecialSearch, v::Vertex; tries::Int = 4, max_vanishing::Int = 100)
  g = state.g
  generic = v.vanishing == 0
  # the hyperelliptic pattern: Rosenhain invariants and the Cartier-Manin matrix
  if v.vanishing == RSM._hyperelliptic_vanishing_count(g)
    lambdas = hyperelliptic_rosenhain(state.field, v.thetas, g)
    if lambdas !== nothing
      f = rosenhain_polynomial(lambdas)
      v.quadrics = f
      v.status = iszero(cartier_manin_matrix(f, g)) ? :jacobian : :hyperelliptic_not_superspecial
      return v
    end
  end
  # many vanishing theta constants: (close to) a product, not tested
  v.vanishing > max_vanishing && (v.status = :many_vanishing; return v)
  rng = Random.MersenneTwister(hash(v.key))
  for trial in 0:(generic ? 0 : tries)
    thetas = v.thetas
    if trial > 0
      M = reduce(*, [RSM._integral_transvection(rand(rng, 0:1, 2 * g), g) for _ in 1:3])
      thetas = transform_thetas(v.thetas, M, g, state.field.zeta8)
    end
    result = try
      reconstruct_exact(thetas, g; require_signs = generic && v.signs_complete, prym_tries = generic ? 300 : 1000)
    catch err
      err isa NeedExtension || rethrow()
      (jacobian = false, stage = :need_extension)
    end
    if result.jacobian
      v.status = :jacobian
      v.quadrics = result.quadrics
      return v
    end
    v.status = Symbol(:not_jacobian_, result.stage)
  end
  return v
end

################################################################################
#  Checks of a hit
################################################################################

@doc raw"""
    hasse_witt_matrix(quadrics) -> matrix

Genus 5, three quadrics in P^4: the Hasse-Witt matrix, entries the
coefficients of x^(p a - b) in (Q_1 Q_2 Q_3)^(p - 1), a, b in
{(1,1,1,1,1) + e_i} (Frobenius on H^4(P^4, O(-6)) = H^1(C, O_C)). The curve
is superspecial iff it vanishes.
"""
function hasse_witt_matrix(quadrics)
  R = parent(quadrics[1])
  K = base_ring(R)
  p = Int(characteristic(K))
  n = nvars(R)
  F = prod(quadrics)^(p - 1)
  index = [[i == j ? 2 : 1 for j in 1:n] for i in 1:n]
  M = zero_matrix(K, n, n)
  for (i, a) in enumerate(index), (j, b) in enumerate(index)
    M[i, j] = coeff(F, p .* a .- b)
  end
  return M
end

function summary(state::SuperspecialSearch)
  counts = Dict{Symbol, Int}()
  for key in state.order
    s = state.vertices[key].status
    counts[s] = get(counts, s, 0) + 1
  end
  vanishing = Dict{Int, Int}()
  for key in state.order
    n = state.vertices[key].vanishing
    vanishing[n] = get(vanishing, n, 0) + 1
  end
  println("p = $(state.p), g = $(state.g): $(state.steps) steps, $(length(state.order)) isomorphism classes")
  println("  status: ", sort(collect(counts); by = string))
  println("  vanishing even theta constants: ", sort(collect(vanishing)))
  return (classes = length(state.order), status = counts, vanishing = vanishing)
end

jacobians(state::SuperspecialSearch) = [state.vertices[k] for k in state.order if state.vertices[k].status == :jacobian]

################################################################################
#  Positive control: superspecial Humbert curves
################################################################################

# The elements of GF(p^2) inside L
function _subfield_elements(L::FqField, d::Int)
  p = Int(characteristic(L))
  w = gen(L)^div(order(L) - 1, big(p)^d - 1)
  return [zero(L); [w^i for i in 0:p^d - 2]]
end

@doc raw"""
    superspecial_humbert_configurations(L; limit = 1) -> Vector

Branch points a = (0, 1, a3, a4, a5) in GF(p^2) of Humbert curves whose
five elliptic quotients y^2 = prod_{j != i} (x - a_j) are supersingular (then
the Humbert curve is superspecial).
"""
function superspecial_humbert_configurations(L::FqField; limit::Int = 1)
  ss = Set(string.(supersingular_lambdas(L)))
  cr(x, y, z, w) = string((w - y) * (z - x) / ((w - x) * (z - y)))   # x, y, z, w -> infinity, 0, 1, lambda
  issing(P) = cr(P...) in ss
  K = _subfield_elements(L, 2)
  found = Vector{Vector{FqFieldElem}}()
  for a3 in K, a4 in K, a5 in K
    a = [zero(L), one(L), a3, a4, a5]
    length(unique(a)) == 5 || continue
    all(i -> issing([a[j] for j in 1:5 if j != i]), 1:5) || continue
    push!(found, a)
    length(found) >= limit && break
  end
  return found
end

@doc raw"""
    humbert_control(p; k = 16) -> NamedTuple

Positive control: a superspecial Humbert curve in characteristic p (if one
exists with branch points in GF(p^2)): glue its supersingular elliptic
quotients, check that the result is found to be a Jacobian, and that the
Hasse-Witt matrix of the reconstructed curve vanishes.
"""
function humbert_control(p::Int; k::Int = 16)
  F = GluingField(p, k)
  configurations = superspecial_humbert_configurations(F.L)
  isempty(configurations) && return (found = false,)
  a = configurations[1]
  pieces, G = humbert_gluing(F, a)
  result = glue_and_reconstruct(F, pieces, G)
  result.jacobian || return (found = true, jacobian = false, branch_points = a)
  HW = hasse_witt_matrix(result.quadrics)
  return (found = true, jacobian = true, branch_points = a, complete_intersection = complete_intersection_check(result.quadrics),
          hasse_witt_zero = iszero(HW), humbert = humbert_check(result.quadrics, a), quadrics = result.quadrics)
end

################################################################################
#  Hyperelliptic vertices
################################################################################

@doc raw"""
    hyperelliptic_rosenhain(F, thetas, g) -> lambdas or nothing

If the even theta constants that vanish have the hyperelliptic pattern: the
Rosenhain invariants (y^2 = x (x - 1) prod (x - lambda)), via Mumford's eta
map in the standard basis (as _rosenhain_invariants, over the field of F).
"""
function hyperelliptic_rosenhain(F::GluingField, thetas, g::Int)
  vanishing = [c for c in keys(thetas) if RSM._is_even(c) && iszero(thetas[c])]
  length(vanishing) == RSM._hyperelliptic_vanishing_count(g) || return nothing
  eta, U = try
    RSM._hyperelliptic_eta(g, thetas, vanishing)
  catch
    return nothing
  end
  standard, U_standard = RSM._mumford_eta_standard(g)
  in_U = sort(setdiff(U, [2*g + 2]))
  order = zeros(Int, 2*g + 1)
  order[2:2:2*g] = in_U
  order[1:2:2*g + 1] = setdiff(1:2*g + 1, in_U)
  N = RSM._symplectic_lift([eta[order[k]] for k in 1:2*g], standard[1:2*g], g)
  J = [zeros(Int, g, g) Matrix{Int}(LinearAlgebra.I, g, g); -Matrix{Int}(LinearAlgebra.I, g, g) zeros(Int, g, g)]
  M = Matrix(transpose(-J * transpose(N) * J))
  moved = transform_thetas(thetas, M, g, F.zeta8)
  squares = Dict(c => v^2 for (c, v) in moved)
  return [RSM._takase_quotient(squares, standard, U_standard, 1, l, 2) for l in 3:2*g+1]
end

# The Cartier-Manin matrix of y^2 = f(x): entries c_(i p - j) of f^((p - 1)/2)
function cartier_manin_matrix(f::PolyRingElem, g::Int)
  K = base_ring(f)
  p = Int(characteristic(K))
  h = f^div(p - 1, 2)
  return matrix(K, g, g, [coeff(h, i * p - j) for i in 1:g for j in 1:g])
end

function rosenhain_polynomial(lambdas)
  K = parent(lambdas[1])
  Kx, x = polynomial_ring(K, :x; cached = false)
  return x * (x - 1) * prod(x - l for l in lambdas)
end

################################################################################
#  Positive control: y^2 = x^p - x (superspecial of genus (p - 1)/2)
################################################################################

@doc raw"""
    hyperelliptic_control(p = 11; k = 16) -> NamedTuple

The superspecial curve y^2 = x^p - x of genus g = (p - 1)/2: theta constants
by Thomae (squares, then signs by Riemann's relations), then the vertex test
(the hyperelliptic pattern, the Rosenhain invariants, Cartier-Manin = 0), and
one step into the isogeny graph from it.
"""
function hyperelliptic_control(p::Int = 11; k::Int = 16)
  F = GluingField(p, k)
  g = div(p - 1, 2)
  a = [F.L(i) for i in 0:p-1]                  # the roots of x^p - x; infinity is the last branch point
  squares = RSM.thomae_theta_constants(a; squares = true)
  L2 = parent(first(values(squares)))
  @req L2 === F.L "The squares need an extension of GF($p^$k)."
  thetas = theta_from_squares(squares)
  _, rank, needed = correct_signs_exact!(thetas, g)
  lambdas = hyperelliptic_rosenhain(F, thetas, g)
  lambdas === nothing && return (signs = (rank, needed), hyperelliptic = false)
  CM = cartier_manin_matrix(rosenhain_polynomial(lambdas), g)
  # one isogeny step
  rng = Random.MersenneTwister(3)
  G = random_lagrangian(g; rng = rng)
  new, r2, n2 = isogenous_thetas(F, thetas, G)
  v = _vertex(F, new, g)
  return (signs = (rank, needed), hyperelliptic = true, cartier_manin_zero = iszero(CM),
          neighbour_vanishing = v.vanishing, neighbour_signs = (r2, n2))
end

################################################################################
#  Other starting points and output
################################################################################

@doc raw"""
    SuperspecialSearch(p, g, thetas; k = 16, seed = 1) -> state

Start from a given (signed) theta null point over GF(p^k), e.g. the
Jacobian of y^2 = x^p - x (see hyperelliptic_start).
"""
function SuperspecialSearch(p::Int, g::Int, thetas::Dict; k::Int = 16, seed::Int = 1)
  F = GluingField(p, k)
  v = _vertex(F, thetas, g)
  state = SuperspecialSearch(p, g, F, Dict(v.key => v), [v.key], v.key, 0, String[], Random.MersenneTwister(seed))
  test_vertex!(state, v)
  return state
end

# The signed theta constants of y^2 = x^p - x (genus (p - 1)/2) over GF(p^k)
function hyperelliptic_start(p::Int; k::Int = 16)
  F = GluingField(p, k)
  squares = RSM.thomae_theta_constants([F.L(i) for i in 0:p-1]; squares = true)
  thetas = theta_from_squares(squares)
  correct_signs_exact!(thetas, div(p - 1, 2))
  return thetas
end

@doc raw"""
    save_state(state, path)

One line per isomorphism class (key, vanishing theta constants, signs
complete, status); the Jacobians (quadrics via export_forms, or the
hyperelliptic polynomial) in path * ".jacobians".
"""
function save_state(state::SuperspecialSearch, path::AbstractString)
  open(path, "w") do io
    println(io, "# p = $(state.p), g = $(state.g), steps = $(state.steps), classes = $(length(state.order))")
    for key in state.order
      v = state.vertices[key]
      println(io, join((key, v.vanishing, v.signs_complete, v.status), "\t"))
    end
  end
  open(path * ".jacobians", "w") do io
    for v in jacobians(state)
      println(io, v.quadrics isa Vector ? export_forms(v.quadrics) : string(v.quadrics))
    end
  end
  return nothing
end

################################################################################
#  The mass formula (Ekedahl, Hashimoto-Ibukiyama)
################################################################################

const _zeta_negative_odd = Dict(1 => 1//12, 3 => 1//120, 5 => 1//252, 7 => 1//240, 9 => 1//132,
                                11 => 691//32760, 13 => 1//12, 15 => 3617//8160)

@doc raw"""
    mass(g, p) -> Rational

The mass sum 1/#Aut(A) over the principally polarized superspecial abelian
varieties of dimension g in characteristic p:
prod_{i=1}^g |zeta(1 - 2i)| / 2 * prod_{i=1}^g (p^i + (-1)^i).
"""
mass(g::Int, p::Int) = prod(_zeta_negative_odd[2i - 1] // 2 for i in 1:g) * prod(big(p)^i + (-1)^i for i in 1:g)
