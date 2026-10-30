################################################################################
#
#  gluing_prototype.jl : gluing curves along 2-torsion over finite fields and
#  reconstructing the glued curve from its theta constants (genus 5)
#
#  Prototype (not part of Hecke). Run with the Hecke checkout that contains
#  src/RieSrf (branch jh/reconstruction-genus-g with Thomae.jl):
#
#     julia --project=/path/to/Hecke gluing_prototype.jl     # the Humbert example
#
#  or include it and call run_humbert_example(p, k) / search_random_gluings(p, k, N).
#
#  Step 1 (gluing_core): theta_A^2 of A = (J_1 x ... x J_r) / G from the theta
#    constants of the pieces: product, Igusa's formula (with a primitive 8th
#    root of unity of the field) to a basis in which G is standard, and
#    theta_A[a;b]^2 = sum_c (-1)^(b.c) theta_B'[c;0] theta_B'[c+a;0].
#    Checked over CC against FLINT (theta constants of M(tau_B)/2) for the
#    genera (1,1,1), (2,1,2), (1,1,1,1,1): agreement to the working precision.
#  Step 2 (exact reconstruction): reconstruct_quadrics_from_thetas with exact
#    linear algebra; LLL for the signs of Riemann's relations replaced by a
#    meet-in-the-middle search; the random search for sign relations without
#    Oscar (orthogonal reflections).
#  Step 3 (demo): elliptic pieces in Legendre form; the Humbert curves give
#    Jacobians (verified: the reconstruction is the Humbert curve);
#    search_random_gluings for random gluings.
#
#  Smoothness of a reconstructed curve: gluing_prototype_verify.jl (Singular,
#  separate environment).
#
################################################################################

using Hecke, Random, LinearAlgebra

################################################################################
#
#  Gluing along 2-torsion with theta constants, over any field
#
#  B = J_1 x ... x J_r (pieces of genus g_i, g = sum g_i) with theta constants
#  theta_i, G a maximal isotropic subspace of B[2] (characteristic
#  coordinates, i.e. (a', b') <-> the point (tau a' + b') / 2). A = B / G is
#  principally polarized. In a symplectic basis of B in which G is
#  L = {(a', 0)} (tau_B' = M tau_B), tau_A = tau_B' / 2 and
#
#     theta_A[a; b]^2 = sum_c (-1)^(b.c) theta_B'[c; 0] theta_B'[c + a; 0]
#
#  (the identity of theta_squares_relations_hold). theta_B' = theta_B moved by
#  Igusa's transformation formula (8th roots of unity) and theta_B is the
#  product of the theta_i. Only rational operations: works over any field
#  that contains a primitive 8th root of unity zeta8 (and the theta_i).
#
################################################################################

const RSM = Hecke.RiemannSurfaces

# Characteristic keys (a..., b...) of genus g
_all_chars(g::Int) = [RSM._char_from_mask(m, g) for m in 0:4^g - 1]

# The theta constants of the product (pieces given as dictionaries of genus
# g_i): theta_B[(a_1..a_r; b_1..b_r)] = prod theta_i[(a_i; b_i)]
function product_thetas(pieces::Vector)
  genera = [RSM._genus_of_thetas(t) for t in pieces]
  g = sum(genera)
  offsets = cumsum([0; genera])
  K = parent(first(values(pieces[1])))
  result = Dict{NTuple{2 * g, Int}, elem_type(K)}()
  for c in _all_chars(g)
    value = one(K)
    for (i, t) in enumerate(pieces)
      gi = genera[i]
      a = c[offsets[i] + 1:offsets[i] + gi]
      b = c[g + offsets[i] + 1:g + offsets[i] + gi]
      value *= t[(a..., b...)]
    end
    result[c] = value
  end
  return result
end

# Igusa's transformation formula with a chosen primitive 8th root of unity:
# the theta constants at M tau from those at tau, up to a common factor
# (_transform_theta_constants with zeta = zeta8 instead of exp(pi i / 4))
function transform_thetas(thetas, M::Matrix{Int}, g::Int, zeta8)
  K = parent(first(values(thetas)))
  powers = [zeta8^k for k in 0:7]
  out = Dict{NTuple{2 * g, Int}, elem_type(K)}()
  for c in _all_chars(g)
    m = collect(c)
    image, phi8 = RSM._igusa_action(M, m, g)
    out[Tuple(RSM._f2(image))] = RSM._reduction_sign(image, g) * powers[mod(phi8, 8) + 1] * thetas[c]
  end
  return out
end

_pair(x, y, g) = RSM._symplectic_pairing(x, y, g)

# A symplectic basis u_1..u_g, v_1..v_g of GF(2)^2g with span(u) = G
# (<u_i, v_j> = delta_ij, <v_i, v_j> = 0); G given by g independent isotropic vectors
function symplectic_completion(G::Vector{Vector{Int}}, g::Int)
  F = GF(2)
  # <u_i, v> = delta_ij: the pairing matrix rows J u_i
  J = [zeros(Int, g, g) Matrix{Int}(LinearAlgebra.I, g, g); Matrix{Int}(LinearAlgebra.I, g, g) zeros(Int, g, g)]
  A = matrix(F, g, 2 * g, reduce(vcat, [transpose(J * u) for u in G]))
  vs = Vector{Int}[]
  for j in 1:g
    rhs = matrix(F, g, 1, [i == j ? 1 : 0 for i in 1:g])
    v = solve(A, rhs; side = :right)
    push!(vs, [Int(lift(ZZ, v[k, 1])) for k in 1:2 * g])
  end
  # make the v isotropic: v_j += <v_i, v_j> u_i (i < j)
  for j in 2:g, i in 1:j - 1
    _pair(vs[i], vs[j], g) == 1 && (vs[j] = RSM._f2(vs[j] + G[i]))
  end
  @assert all(_pair(G[i], vs[j], g) == (i == j ? 1 : 0) for i in 1:g, j in 1:g)
  @assert all(_pair(vs[i], vs[j], g) == 0 for i in 1:g, j in 1:g)
  @assert all(_pair(G[i], G[j], g) == 0 for i in 1:g, j in 1:g)
  return vs
end

# M in Sp(2g, Z) (acting on tau) whose action on characteristics maps G to
# L = {(a', 0)} (u_i -> e_i, v_i -> e_(g+i))
function kernel_to_standard(G::Vector{Vector{Int}}, g::Int)
  vs = symplectic_completion(G, g)
  e(i) = [k == i ? 1 : 0 for k in 1:2 * g]
  N = RSM._symplectic_lift([G; vs], [e(i) for i in 1:2 * g], g)
  J = [zeros(Int, g, g) Matrix{Int}(LinearAlgebra.I, g, g); -Matrix{Int}(LinearAlgebra.I, g, g) zeros(Int, g, g)]
  return Matrix(transpose(-J * transpose(N) * J))
end

# theta_A^2 from theta_B' (G standard): sum_c (-1)^(b.c) theta[c;0] theta[c+a;0]
function halving_squares(thetas_moved, g::Int)
  K = parent(first(values(thetas_moved)))
  bits = [collect(RSM._char_from_mask(m, g))[1:g] for m in 0:2^g - 1]
  result = Dict{NTuple{2 * g, Int}, elem_type(K)}()
  for a in bits, b in bits
    s = zero(K)
    for c in bits
      term = thetas_moved[Tuple([c; zeros(Int, g)])] * thetas_moved[Tuple([RSM._f2(c + a); zeros(Int, g)])]
      s += isodd(sum(b .* c)) ? -term : term
    end
    result[Tuple([a; b])] = s
  end
  return result
end

@doc raw"""
    glue_theta_squares(pieces, G, zeta8) -> Dict, Matrix

The squares of the theta constants of A = (J_1 x ... x J_r) / G (projective)
and the matrix M (tau_A = M(tau_B) / 2).
"""
function glue_theta_squares(pieces::Vector, G::Vector{Vector{Int}}, zeta8)
  thetas_B = product_thetas(pieces)
  g = RSM._genus_of_thetas(thetas_B)
  M = kernel_to_standard(G, g)
  moved = transform_thetas(thetas_B, M, g, zeta8)
  return halving_squares(moved, g), M
end

# A random maximal isotropic subspace of GF(2)^2g (basis), via a random
# symplectic image of L = {(a', 0)}
function random_lagrangian(g::Int; rng = Random.default_rng())
  vectors = [collect(RSM._char_from_mask(m, g)) for m in 1:4^g - 1]
  basis = [[k == i ? 1 : 0 for k in 1:2 * g] for i in 1:g]
  for _ in 1:8 * g
    v = vectors[rand(rng, 1:length(vectors))]
    # transvection x -> x + <x, v> v
    basis = [RSM._f2(x + _pair(x, v, g) * v) for x in basis]
  end
  return basis
end

# Whether G meets J_i[2] (the coordinates of piece i) trivially for all i
function transverse_to_pieces(G::Vector{Vector{Int}}, genera::Vector{Int})
  g = sum(genera)
  offsets = cumsum([0; genera])
  span = [reduce((x, y) -> RSM._f2(x + y), G[findall(isodd, digits(m; base = 2, pad = g))]; init = zeros(Int, 2 * g)) for m in 1:2^g - 1]
  for (i, gi) in enumerate(genera)
    inside(x) = all(iszero(x[k]) for k in 1:g if !(offsets[i] < k <= offsets[i] + gi)) &&
                all(iszero(x[g + k]) for k in 1:g if !(offsets[i] < k <= offsets[i] + gi))
    any(inside, span) && return false
  end
  return true
end

# Whether G is in general position with respect to the pieces: for every set
# I of pieces, dim (G meet B_I[2]) = max(0, dim G - 2 (g - g_I)) (the
# dimension for a generic Lagrangian); special positions give abelian
# varieties with vanishing theta constants
function general_position(G::Vector{Vector{Int}}, genera::Vector{Int})
  g = sum(genera)
  offsets = cumsum([0; genera])
  r = length(genera)
  F = GF(2)
  for mask in 1:2^r - 2
    I = findall(isodd, digits(mask; base = 2, pad = r))
    gI = sum(genera[I])
    outside = [k for k in 1:g if !any(offsets[i] < k <= offsets[i] + genera[i] for i in I)]
    # G meet B_I[2]: the combinations of the basis vanishing on the coordinates outside I
    A = matrix(F, length(G), 2 * length(outside), [x[k + s] for x in G for s in (0, g) for k in outside])
    dim_meet = length(G) - rank(A)
    dim_meet == max(0, g - 2 * (g - gI)) || return false
  end
  return true
end

################################################################################
#
#  The reconstruction of genus g >= 5 (Quadrics.jl) over an exact field
#
#  The same steps as reconstruct_quadrics_from_thetas, with exact linear
#  algebra (FqField):
#   1. the gradients of the odd theta functions: the kernel of all of Fay's
#      relations of the rho of _fay_rhos (no selection of a basis needed);
#   2. the Prym theta constants by Schottky-Jung (square roots), signs from
#      Riemann's relations with the stored sign data: the +-1 coefficients of
#      a relation, found by LLL over CC, are found here by a meet-in-the-middle
#      search (exact zero test);
#   3. the quadrics from the relations between the squares of the Prym
#      gradients.
#  Exact ranks make this a Jacobian test: the Fay kernel has dimension g and
#  the relation matrix rank (g - 2)(g - 3)/2 for a (generic) Jacobian.
#
#  Square roots that do not exist in the field throw NeedExtension: choose the
#  field large enough (e.g. GF(p, 16)); a large field also makes the
#  meet-in-the-middle search unambiguous.
#
################################################################################

struct NeedExtension <: Exception end

function _sqrt_exact(x)
  iszero(x) && return x
  ok, r = is_square_with_sqrt(x)
  ok || throw(NeedExtension())
  return r
end

# The theta constants from their squares: arbitrary signs
theta_from_squares(thetas_sq::Dict) = Dict(c => _sqrt_exact(v) for (c, v) in thetas_sq)

################################################################################
#  Exact Riemann relations and the sign correction
################################################################################

# The +-1 coefficients s (s[fixed] = 1) with sum_i s_i v_i = 0, all solutions
function _pm_solutions(values::Vector{T}, fixed::Int) where T
  others = [i for i in eachindex(values) if i != fixed]
  half = div(length(others), 2)
  H1, H2 = others[1:half], others[half+1:end]
  # all signed sums over H1 (with the fixed term) and over H2
  function sums(H, start)
    result = Vector{Tuple{T, UInt64}}(undef, 2^length(H))
    s = start + sum((values[i] for i in H); init = zero(start))   # all signs +
    mask = UInt64(0)
    result[1] = (s, mask)
    for k in 1:2^length(H) - 1
      j = trailing_zeros(k) + 1          # Gray code: flip bit j
      bit = UInt64(1) << (j - 1)
      if mask & bit == 0
        s -= 2 * values[H[j]]
      else
        s += 2 * values[H[j]]
      end
      mask ⊻= bit
      result[k + 1] = (s, mask)
    end
    return result
  end
  S1 = sums(H1, values[fixed])
  S2 = sums(H2, zero(values[fixed]))
  table = Dict{T, Vector{UInt64}}()
  for (s, m) in S2
    push!(get!(table, -s, UInt64[]), m)
  end
  solutions = Vector{Dict{Int, Int}}()
  for (s, m1) in S1
    haskey(table, s) || continue
    for m2 in table[s]
      sol = Dict(fixed => 1)
      for (j, i) in enumerate(H1); sol[i] = (m1 >> (j - 1)) & 1 == 1 ? -1 : 1; end
      for (j, i) in enumerate(H2); sol[i] = (m2 >> (j - 1)) & 1 == 1 ? -1 : 1; end
      push!(solutions, sol)
    end
  end
  return solutions
end

# The relation of (term, data) with exact values (cf. _relation_for_data):
# [(sorted indices of the four characteristics, +-1)], the term with +1
function exact_relation(thetas, term, data)
  fixed_term = sort([RSM.char_to_index(collect(c)) for c in term])
  position = findfirst(==(fixed_term), data.term_tup)
  (position === nothing || data.coefficients[position] == 0) && return nothing
  all(allunique, data.term_tup) || return nothing
  K = parent(first(values(thetas)))
  values_all = [c == 0 ? zero(K) : c * prod(thetas[Tuple(k)] for k in ks) for (c, ks) in zip(data.coefficients, data.keys)]
  support = findall(!iszero, values_all)
  (position in support && length(support) >= 2) || return nothing
  fixed = findfirst(==(position), support)
  solutions = _pm_solutions(values_all[support], fixed)
  length(solutions) == 1 || return nothing      # none (not a theta null point) or ambiguous
  sol = solutions[1]
  return sort!([(data.term_tup[support[i]], sol[i]) for i in eachindex(support)])
end

@doc raw"""
    correct_signs_exact!(thetas, g; pairs = stored sign data of genus g) -> thetas, rank, needed

Exact version of correct_signs_with_data!: the stored pairs, then random
pairs (random isometries without Oscar) until the rank is full.
"""
function correct_signs_exact!(thetas, g::Int; pairs = RSM.load_sign_data(RSM._default_sign_data_file(g)),
                             max_tries::Int = 20000, rng = Random.MersenneTwister(7))
  fixed_thetas, non_fixed_thetas = RSM.find_fixed_even_chars(g)
  filter!(c -> !iszero(thetas[Tuple(c)]), non_fixed_thetas)
  S = RSM._SignSystem(g, RSM.char_to_index.(non_fixed_thetas))
  target = length(non_fixed_thetas)
  for (term, M1) in pairs
    S.rank >= target && break
    rel = exact_relation(thetas, term, RSM._relation_terms_int(g, term, M1))
    rel === nothing || RSM._add_relation!(S, rel)
  end
  # the stored pairs were chosen for generic curves (no vanishing theta
  # constants), they need not suffice here: random pairs as in
  # _random_search!, with random isometries of x'y from orthogonal reflections
  tries = 0
  if S.rank < target
    F = GF(2)
    terms = RSM.find_zero_sum_tetrads(fixed_thetas)
    v1 = F.(ZZ.(RSM.max_noether_characteristics(g)[1] * 2))
    to_term = Dict{Any, FqMatrix}()
    while S.rank < target && tries < max_tries
      tries += 1
      term = terms[rand(rng, 1:length(terms))]
      M = get!(() -> RSM.map_even_characteristic(v1, F.(collect(term[1]))), to_term, term[1])
      M1 = random_isometry(g; rng = rng) * M
      rel = exact_relation(thetas, term, RSM._relation_terms_int(g, term, M1))
      rel === nothing || RSM._add_relation!(S, rel)
    end
  end
  RSM._apply_signs!(thetas, S, non_fixed_thetas)
  return thetas, S.rank, target
end

# A random element of the orthogonal group of q(x) = x[1:g]'x[g+1:2g] over
# GF(2): a product of reflections x -> x + B(x, v) v with q(v) = 1
function random_isometry(g::Int; rng = Random.default_rng(), length::Int = 6 * g)
  F = GF(2)
  Jp = [zeros(Int, g, g) Matrix{Int}(LinearAlgebra.I, g, g); Matrix{Int}(LinearAlgebra.I, g, g) zeros(Int, g, g)]
  R = Matrix{Int}(LinearAlgebra.I, 2 * g, 2 * g)
  count = 0
  while count < length
    v = rand(rng, 0:1, 2 * g)
    isodd(sum(v[i] * v[g + i] for i in 1:g)) || continue
    R = mod.((Matrix{Int}(LinearAlgebra.I, 2 * g, 2 * g) + v * transpose(Jp * v)) * R, 2)
    count += 1
  end
  return matrix(F, R)
end

################################################################################
#  Fay's relations: the gradients of the odd theta functions
################################################################################

@doc raw"""
    exact_gradient_kernel(g, thetas) -> matrix

The kernel of Fay's relations (rows: the odd characteristics, as in
odd_theta_gradient_kernel), all relations of the rho of _fay_rhos(g).
"""
const _fay_structures = Dict{Int, Any}()

function exact_gradient_kernel(g::Int, thetas; extra::Int = 40, rng = Random.MersenneTwister(1))
  K = parent(first(values(thetas)))
  odd_indices = RSM.char_to_index.(collect.(RSM.odd_theta_characteristics(g)))
  n = length(odd_indices)
  position = Dict(c => k for (k, c) in enumerate(odd_indices))
  structure = get!(() -> reduce(vcat, [RSM.fay_matrix_structure(g, rho) for rho in RSM._fay_rhos(g)]), _fay_structures, g)
  function rows(selection)
    A = zero_matrix(K, length(selection), n)
    for (r, s) in enumerate(selection), (column, coefficient, c1, c2, c3) in structure[s]
      k = get(position, column, 0)
      k == 0 && continue
      A[r, k] += coefficient * (thetas[c1] * thetas[c2] * thetas[c3])
    end
    return A
  end
  # the kernel of a random subset of the relations (n - g + extra), then all
  # relations are checked; more rows if the kernel is too large
  order = Random.shuffle(rng, collect(1:length(structure)))
  count = min(length(structure), n - g + extra)
  while true
    Ksub = kernel(rows(order[1:count]); side = :right)
    # check all relations, in chunks (the full matrix is large over big fields)
    if all(c -> iszero(rows(order[c:min(c + 255, end)]) * Ksub), 1:256:length(order))
      return Ksub
    end
    count == length(structure) && return Ksub   # cannot happen: the full system
    count = min(length(structure), 2 * count)
  end
end

################################################################################
#  The Prym and the quadrics
################################################################################

function exact_prym_thetas(g::Int, thetas)
  K = parent(first(values(thetas)))
  result = Dict{NTuple{2 * (g - 1), Int}, elem_type(K)}()
  for d in RSM.even_theta_characteristics(g - 1)
    result[d] = _sqrt_exact(thetas[(0, d[1:g-1]..., 0, d[g:2*(g-1)]...)] *
                            thetas[(0, d[1:g-1]..., 1, d[g:2*(g-1)]...)])
  end
  for d in RSM.odd_theta_characteristics(g - 1)
    result[d] = zero(K)
  end
  return result
end

# The quadrics (cf. _quadrics_from_gradients) and the rank of the relation matrix
function exact_quadrics(g::Int, Kg, K_prym)
  F = base_ring(Kg)
  lower(n) = [(i, j) for j in 1:n for i in j:n]
  index_pairs = RSM.lift_prym_indices(g)
  n = length(index_pairs)
  products = zero_matrix(F, n, length(lower(g)))
  squares = zero_matrix(F, n, length(lower(g - 1)))
  for (d, (i1, i2)) in enumerate(index_pairs)
    for (k, (a, b)) in enumerate(lower(g))
      products[d, k] = Kg[i1, a] * Kg[i2, b] + Kg[i2, a] * Kg[i1, b]
    end
    for (k, (a, b)) in enumerate(lower(g - 1))
      squares[d, k] = K_prym[d, a] * K_prym[d, b]
    end
  end
  O = kernel(transpose(squares); side = :right)          # relations between the squares
  relation_matrix = transpose(O) * products
  r, E = rref(relation_matrix)
  R, x = polynomial_ring(F, ["x$i" for i in 1:g]; cached = false)
  half = inv(F(2))
  quadrics = [sum((a == b ? half : one(F)) * E[i, k] * x[a] * x[b] for (k, (a, b)) in enumerate(lower(g))) for i in 1:r]
  return quadrics, r, ncols(O)
end

@doc raw"""
    reconstruct_exact(thetas, g) -> NamedTuple

The exact reconstruction from signed theta constants of genus g >= 5 (over
an FqField): `jacobian` (the ranks are those of a generic Jacobian), the
quadrics and the ranks.
"""
function reconstruct_exact(thetas, g::Int; verbose::Bool = false, prym_tries::Int = 300, require_signs::Bool = true)
  expected = div((g - 2) * (g - 3), 2)
  thetas_P = exact_prym_thetas(g, thetas)
  _, rank_P, needed_P = correct_signs_exact!(thetas_P, g - 1; max_tries = prym_tries)
  verbose && println("  Prym signs: rank $rank_P of $needed_P")
  require_signs && rank_P < needed_P && return (jacobian = false, stage = :prym_signs, rank = rank_P, needed = needed_P)
  Kg = exact_gradient_kernel(g, thetas)
  verbose && println("  Fay kernel: dimension $(ncols(Kg)) (Jacobian: $g)")
  ncols(Kg) == g || return (jacobian = false, stage = :fay, fay_dimension = ncols(Kg))
  K_prym = exact_gradient_kernel(g - 1, thetas_P)
  verbose && println("  Prym Fay kernel: dimension $(ncols(K_prym)) (expected $(g - 1))")
  ncols(K_prym) == g - 1 || return (jacobian = false, stage = :prym_fay, prym_fay_dimension = ncols(K_prym))
  quadrics, r, relations = exact_quadrics(g, Kg, K_prym)
  verbose && println("  quadrics: rank $r (Jacobian: $expected)")
  return (jacobian = r == expected, stage = :quadrics, quadrics = quadrics, rank = r,
          gradients = Kg, prym_gradients = K_prym, prym_thetas = thetas_P)
end

################################################################################
#  Checks of the reconstructed model
################################################################################

# The dimension of the degree d part of the ideal generated by the forms
function _ideal_dimension(forms, d::Int)
  R = parent(forms[1])
  F = base_ring(R)
  n = nvars(R)
  monomials(k) = k == 0 ? [one(R)] : unique([m * x for m in monomials(k - 1) for x in gens(R)])
  target = monomials(d)
  index = Dict(m => i for (i, m) in enumerate(target))
  e = d - total_degree(forms[1])
  products = [m * q for q in forms for m in monomials(e)]
  A = zero_matrix(F, length(products), length(target))
  for (r, f) in enumerate(products), (c, m) in zip(coefficients(f), monomials_iter(f))
    A[r, index[m]] = c
  end
  return rank(A), length(target)
end
monomials_iter(f) = Hecke.AbstractAlgebra.monomials(f)

@doc raw"""
    complete_intersection_check(quadrics) -> Bool

Genus 5: whether the Hilbert function of the three quadrics in P^4 in
degrees 2, 3, 4 is 8d - 4, that of a complete intersection curve of degree 8
and arithmetic genus 5. (Smoothness: see gluing_prototype_verify.jl.)
"""
function complete_intersection_check(quadrics)
  all(d -> begin
        r, n = _ideal_dimension(quadrics, d)
        n - r == 8 * d - 4
      end, 2:4)
end


# The quadrics as plain data: the defining polynomial of the field (integer
# coefficients) and per quadric [(exponents, coefficients of the element in z)]
function export_forms(forms)
  F = base_ring(parent(forms[1]))
  f = defining_polynomial(F)
  def = [Int(lift(ZZ, coeff(f, i))) for i in 0:degree(f)]
  elem(c) = [Int(lift(ZZ, coeff(c, i))) for i in 0:degree(F) - 1]
  data = [[(exponent_vector(q, i), elem(coeff(q, i))) for i in 1:length(q)] for q in forms]
  return (characteristic = Int(characteristic(F)), defining = def, forms = data)
end

################################################################################
#
#  Step 3: end to end over a finite field
#
#  Elliptic pieces in Legendre form y^2 = x (x - 1) (x - lambda): theta_00 = 1,
#  theta_10 = lambda^(1/4), theta_01 = (1 - lambda)^(1/4), theta_11 = 0 (every
#  choice of fourth roots is the theta null point of some tau in the
#  Gamma(2)-orbit, i.e. the same labeling of the 2-torsion). All computations
#  in L = GF(p, k), which must contain a primitive 8th root of unity, the
#  fourth roots and the square roots (k = 16 works for small p).
#
################################################################################

struct GluingField
  L::FqField
  zeta8::FqFieldElem
end

function GluingField(p::Int, k::Int)
  L, _ = finite_field(p, k, "z")
  Lx, X = polynomial_ring(L, :X)
  zeta8 = first(r for r in roots(X^8 - 1) if !isone(r^4))
  return GluingField(L, zeta8)
end

function _fourth_root(F::GluingField, c)
  Lx, X = polynomial_ring(F.L, :X)
  r = roots(X^4 - F.L(c))
  isempty(r) && throw(NeedExtension())
  return r[1]
end

legendre_thetas(F::GluingField, lambda) =
  Dict((0, 0) => one(F.L), (1, 0) => _fourth_root(F, lambda), (0, 1) => _fourth_root(F, 1 - F.L(lambda)), (1, 1) => zero(F.L))

@doc raw"""
    glue_and_reconstruct(F, pieces, G; tries = 12, verbose = false) -> NamedTuple

theta_A^2 by gluing, theta_A (square roots, signs by Riemann's relations),
then the exact reconstruction. The Prym of eta = (0..0; 1 0..0) can be
degenerate for special curves (e.g. curves with vanishing theta constants):
then theta_A is moved by random symplectic matrices (another eta) and the
reconstruction repeated, at most `tries` times. `skip_vanishing`: give up at
once if an even theta constant of A vanishes.
"""
function glue_and_reconstruct(F::GluingField, pieces, G; tries::Int = 12, verbose::Bool = false,
                              skip_vanishing::Bool = false, rng = Random.MersenneTwister(5))
  g = length(G)
  squares, _ = glue_theta_squares(pieces, G, F.zeta8)
  vanishing = count(c -> RSM._is_even(c) && iszero(squares[c]), keys(squares))
  skip_vanishing && vanishing > 0 && return (jacobian = false, stage = :vanishing_theta, vanishing = vanishing)
  thetas = theta_from_squares(squares)
  _, rank_A, needed_A = correct_signs_exact!(thetas, g)
  verbose && println("vanishing even theta constants: $vanishing; signs of A: rank $rank_A of $needed_A")
  generic = vanishing == 0
  for trial in 0:tries
    moved = thetas
    if trial > 0
      M = reduce(*, [RSM._integral_transvection(rand(rng, 0:1, 2 * g), g) for _ in 1:3])
      moved = transform_thetas(thetas, M, g, F.zeta8)
    end
    result = reconstruct_exact(moved, g; verbose = verbose, require_signs = generic,
                               prym_tries = generic ? 300 : 2000)
    result.jacobian && return merge(result, (thetas = moved, vanishing = vanishing, eta_trials = trial))
    # for a generic A one eta suffices to decide
    generic && return merge(result, (vanishing = vanishing,))
  end
  return (jacobian = false, stage = :no_eta, vanishing = vanishing)
end

################################################################################
#  The Humbert curves: a known Jacobian among the gluings
################################################################################

@doc raw"""
    humbert_gluing(F, a) -> pieces, G

The Humbert curve with branch points a_1..a_5 (the (Z/2)^4-cover of P^1,
genus 5, the intersection of the quadrics sum x_i^2, sum a_i x_i^2,
sum a_i^2 x_i^2) has a Jacobian isogenous to E_1 x ... x E_5,
E_i: y^2 = prod_{j != i} (x - a_j). Its Jacobian is (E_1 x ... x E_5) / G for
the S_5-invariant G spanned by g_jk = sum_{i not in {j, k}} e^(i)_jk, with
e^(i)_jk the 2-torsion point of a_j, a_k on E_i (found experimentally: it is
isotropic, of dimension 5, in general position, and the reconstruction gives
back the Humbert curve).
"""
function humbert_gluing(F::GluingField, a::Vector)
  a = F.L.(a)
  pieces = Any[]
  label = Dict{Tuple{Int, Int, Int}, Vector{Int}}()
  for i in 1:5
    P = [j for j in 1:5 if j != i]
    # P_1, P_2, P_3, P_4 -> infinity, 0, 1, lambda
    m(x) = (x - a[P[2]]) * (a[P[3]] - a[P[1]]) / ((x - a[P[1]]) * (a[P[3]] - a[P[2]]))
    push!(pieces, legendre_thetas(F, m(a[P[4]])))
    # (characteristic coordinates of E_i[2]: x = 0 <-> (1;0), x = 1 <-> (0;1), x = lambda <-> (1;1))
    characteristic = Dict(2 => [1, 0], 3 => [0, 1], 4 => [1, 1])
    for q in 2:4
      r = setdiff(2:4, [q])
      label[(i, minmax(P[1], P[q])...)] = characteristic[q]
      label[(i, minmax(P[r[1]], P[r[2]])...)] = characteristic[q]
    end
  end
  function g_vector(j, k)
    v = zeros(Int, 10)
    for i in 1:5
      i in (j, k) && continue
      c = label[(i, j, k)]
      v[i] = mod(v[i] + c[1], 2)
      v[5 + i] = mod(v[5 + i] + c[2], 2)
    end
    return v
  end
  spanning = [g_vector(j, k) for j in 1:5 for k in j+1:5]
  r, E = rref(matrix(GF(2), 10, 10, reduce(vcat, [transpose(v) for v in spanning])))
  G = [[Int(lift(ZZ, E[i, c])) for c in 1:10] for i in 1:r]
  @assert r == 5 && all(_pair(x, y, 5) == 0 for x in G, y in G)
  return pieces, G
end

# The discriminant of the net of quadrics (a quintic in t1, t2, t3) and its factors
function net_discriminant(quadrics)
  K = base_ring(parent(quadrics[1]))
  n = nvars(parent(quadrics[1]))
  T, t = polynomial_ring(K, ["t$i" for i in 1:length(quadrics)]; cached = false)
  function symmetric(q)
    S = zero_matrix(T, n, n)
    for (c, e) in zip(coefficients(q), Hecke.AbstractAlgebra.exponent_vectors(q))
      idx = findall(!iszero, e)
      if length(idx) == 1
        S[idx[1], idx[1]] += c
      else
        S[idx[1], idx[2]] += c * inv(K(2))
        S[idx[2], idx[1]] += c * inv(K(2))
      end
    end
    return S
  end
  D = det(sum(t[i] * symmetric(q) for (i, q) in enumerate(quadrics)))
  return D, factor(D)
end

# For a Humbert curve the discriminant of the net is 5 lines whose dual points
# lie on a conic with the cross-ratios of a: compare the j-invariants of the
# 4-point subsets
function humbert_check(quadrics, a)
  K = base_ring(parent(quadrics[1]))
  a = K.(a)
  D, fac = net_discriminant(quadrics)
  lines = [f for (f, e) in fac if total_degree(f) == 1 && e == 1]
  length(lines) == 5 || return false
  P = [[coeff(f, [1, 0, 0]), coeff(f, [0, 1, 0]), coeff(f, [0, 0, 1])] for f in lines]
  cross(u, v) = [u[2]*v[3] - u[3]*v[2], u[3]*v[1] - u[1]*v[3], u[1]*v[2] - u[2]*v[1]]
  d2(u, v) = u[1]*v[2] - u[2]*v[1]
  # the cross-ratio of the points i on the conic, seen from the point o
  function cross_ratio(i, o)
    w = [cross(P[o], P[k]) for k in i]
    pairs = [(1, 2), (1, 3), (2, 3)]
    pr = pairs[findfirst(pq -> !iszero(w[1][pq[1]]*w[2][pq[2]] - w[1][pq[2]]*w[2][pq[1]]), pairs)]
    s = [(x[pr[1]], x[pr[2]]) for x in w]
    return d2(s[1], s[3]) * d2(s[2], s[4]) / (d2(s[1], s[4]) * d2(s[2], s[3]))
  end
  j_invariant(l) = 256 * (l^2 - l + 1)^3 / (l^2 * (l - 1)^2)
  cross_ratio_a(i) = ((a[i[1]] - a[i[3]]) * (a[i[2]] - a[i[4]])) / ((a[i[1]] - a[i[4]]) * (a[i[2]] - a[i[3]]))
  others(o) = [k for k in 1:5 if k != o]
  js_curve = sort(string.([j_invariant(cross_ratio(others(o), o)) for o in 1:5]))
  js_a = sort(string.([j_invariant(cross_ratio_a(others(o))) for o in 1:5]))
  return js_curve == js_a
end

@doc raw"""
    run_humbert_example(p = 13, k = 16; a = random) -> NamedTuple

End to end: glue the five elliptic quotients of a Humbert curve over GF(p)
(computations in GF(p^k)), reconstruct, and check that the quadrics define a
complete intersection of degree 8 and genus 5 whose net has the discriminant
(5 lines, same cross-ratios) of the Humbert curve with branch points a.
"""
function run_humbert_example(p::Int = 13, k::Int = 16; a = nothing, verbose::Bool = true)
  F = GluingField(p, k)
  a === nothing && (a = sort(Random.randperm(Random.MersenneTwister(1), p)[1:5] .- 1))
  verbose && println("Humbert curve over GF($p), branch points $a")
  pieces, G = humbert_gluing(F, a)
  result = glue_and_reconstruct(F, pieces, G; verbose = verbose)
  result.jacobian || return result
  ci = complete_intersection_check(result.quadrics)
  humbert = humbert_check(result.quadrics, a)
  verbose && println("Jacobian (3 quadrics): true; complete intersection of degree 8, genus 5: $ci; " *
                     "the Humbert curve of a: $humbert")
  return merge(result, (complete_intersection = ci, humbert = humbert, branch_points = a, field = F))
end

@doc raw"""
    search_random_gluings(p, k, N; seed = 3) -> Dict

N random gluings of 5 elliptic curves y^2 = x (x - 1) (x - lambda),
lambda in GF(p) (full rational 2-torsion, so every G is defined over GF(p)),
with random Lagrangians G: statistics of the outcome (special position,
vanishing theta constants, the stage at which the Jacobian test failed, or a
Jacobian). Hits are printed and returned.
"""
function search_random_gluings(p::Int, k::Int, N::Int; seed::Int = 3, verbose::Bool = true)
  F = GluingField(p, k)
  rng = Random.MersenneTwister(seed)
  genera = [1, 1, 1, 1, 1]
  stats = Dict{Symbol, Int}()
  hits = Any[]
  last = time()
  for trial in 1:N
    lambdas = [rand(rng, 2:p-1) for _ in 1:5]
    G = random_lagrangian(5; rng = rng)
    outcome = if !general_position(G, genera)
      :special_position
    else
      pieces = [legendre_thetas(F, l) for l in lambdas]
      result = glue_and_reconstruct(F, pieces, G; tries = 0, skip_vanishing = true)
      if result.jacobian
        push!(hits, (lambdas = lambdas, G = G, quadrics = result.quadrics))
        verbose && println("HIT: lambdas = $lambdas, G = $G")
        :jacobian
      else
        result.vanishing > 0 ? :vanishing_theta : result.stage
      end
    end
    stats[outcome] = get(stats, outcome, 0) + 1
    if verbose && time() - last > 60
      println("$trial: $stats")
      last = time()
    end
  end
  return (stats = stats, hits = hits)
end

if abspath(PROGRAM_FILE) == @__FILE__
  run_humbert_example()
end
