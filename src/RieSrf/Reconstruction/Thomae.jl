################################################################################
#
#  Thomae.jl : theta constants of hyperelliptic curves over any field
#
#  Thomae's formula gives the theta constants of a hyperelliptic curve
#  y^2 = f(x) algebraically in terms of its branch points, so it makes sense
#  over any field of characteristic != 2 (e.g. a finite field) and the output
#  can be fed to the algebraic parts of the reconstruction.
#
#  Conventions (as in Hyperelliptic.jl): the branch points a_1, ..., a_2g+1
#  (a_2g+2 = infinity) are labeled by Mumford's eta map in the standard
#  symplectic basis (_mumford_eta_standard) and U = {2, 4, .., 2g, 2g + 2}.
#  For S of size g + 1 the even characteristic eta_U + eta_S has
#
#     theta[eta_U + eta_S]^4 = c * prod_{i < j in S} (a_j - a_i) * prod_{i < j not in S} (a_j - a_i)
#
#  (products over the finite branch points, c independent of S); all other
#  theta constants vanish. Checked against the FLINT theta constants of the
#  period matrix moved to Mumford's basis (test/RieSrf/Reconstruction/Thomae.jl).
#
#  The squares theta^2 need a consistent choice of the square roots: they are
#  fixed by Takase's formula (_takase_quotient), which says that for distinct
#  finite k, l, m and any partition of the other 2g - 2 finite branch points
#  into V, W of size g - 1
#
#     sign * theta^2(V+kl) theta^2(W+kl) / (theta^2(V+km) theta^2(W+km)) = (a_l - a_k) / (a_m - a_k).
#
#  Writing theta^2(S) = s_S t_S with t_S a fixed square root of theta^4(S),
#  these are linear equations over GF(2) for the signs s_S. With all
#  partitions their solutions are (checked for g <= 6) exactly the sign changes
#  theta[m]^2 -> (-1)^(e + v.m) theta[m]^2 (e in GF(2), v in GF(2)^2g) of a
#  particular solution: the common sign and the signs that are linear in the
#  characteristic, i.e. the ambiguity of the theta^2 given the labeling. The
#  result is checked with the quadratic relations between the theta^2 and the
#  second order theta constants Theta[c](2 tau) (theta_squares_relations_hold).
#
#  Ported from (and generalizing to any g) the genus 2 Thomae formulas of
#  AbelianVariety.from_curve in thetAV (Sage), which works with Rosenhain
#  models of genus 2 curves only.
#
#  Characteristics are the keys of Hecke.thetas: tuples (a..., b...) with a
#  the part that shifts the lattice (theta[a; b](tau) = sum_n
#  exp(pi i (n + a/2) tau (n + a/2) + pi i (n + a/2) . b)).
#
################################################################################

# The branch points with the last one at infinity (2g + 1 of them): a list of
# 2g + 2 finite points is moved by x -> 1 / (x - a_2g+2); the theta constants
# (of the curve with the same labeling) do not change.
function _branch_points_with_infinity(a::Vector)
  n = length(a)
  @req n >= 5 "At least 5 branch points are needed (genus >= 2)."
  if iseven(n)
    infinity = a[end]
    @req all(!=(infinity), a[1:end-1]) "The branch points must be distinct."
    return [inv(x - infinity) for x in a[1:end-1]]
  end
  return a
end

function _check_branch_points(a::Vector)
  K = parent(a[1])
  @req characteristic(K) != 2 "Thomae's formula needs characteristic != 2."
  @req length(unique(a)) == length(a) "The branch points must be distinct."
  return K
end

# The characteristic eta_U + eta_S (S a set of labels of size g + 1)
function _thomae_characteristic(eta, U, S, g::Int)
  return Tuple(_f2(sum((eta[i] for i in symdiff(U, S)); init = zeros(Int, 2 * g))))
end

# The sets S of size g + 1 that contain 2g + 2: one for each even nonvanishing
# theta constant (S and its complement give the same characteristic)
_thomae_sets(g::Int) = [[S; 2 * g + 2] for S in _subsets(2 * g + 1, g)]

# prod_{i < j in S, both finite} (a_j - a_i)
function _thomae_product(a::Vector, S::Vector{Int})
  finite = sort([i for i in S if i <= length(a)])
  result = one(parent(a[1]))
  for x in eachindex(finite), y in x+1:length(finite)
    result *= a[finite[y]] - a[finite[x]]
  end
  return result
end

function _thomae_fourth_powers(a::Vector)
  g = div(length(a) - 1, 2)
  eta, U = _mumford_eta_standard(g)
  everything = collect(1:2 * g + 2)
  K = parent(a[1])
  result = Dict{NTuple{2 * g, Int}, elem_type(K)}()
  for mask in 0:4^g - 1
    result[_char_from_mask(mask, g)] = zero(K)
  end
  for S in _thomae_sets(g)
    result[_thomae_characteristic(eta, U, S, g)] = _thomae_product(a, S) * _thomae_product(a, setdiff(everything, S))
  end
  return result
end

@doc raw"""
    thomae_theta_constants(a::Vector; squares::Bool = false, check::Bool = true) -> Dict

The theta constants of the hyperelliptic curve with branch points `a` (a
vector of 2g + 1 elements of a field K of characteristic != 2, the branch point
2g + 2 being at infinity, or 2g + 2 elements), labeled by Mumford's eta map in
the standard symplectic basis (see Hyperelliptic.jl), by Thomae's formula: the
fourth powers theta[c]^4, or with `squares = true` the squares theta[c]^2
(signs fixed by Takase's formula). The keys are the characteristics as in
Hecke.thetas; the values are projective (up to a common factor) and lie in K,
except for the squares over a finite field, where they are in the quadratic
extension of K if necessary (the square roots of the fourth powers must exist
in K for other fields). With `check = true` the squares are checked with
theta_squares_relations_hold (8^g products: switch off for large g).

The fourth powers are the analogue over K of the theta constants of the
period matrix after `_transform_theta_constants` to Mumford's basis, as used in
`_rosenhain_invariants`; `rosenhain_invariants_from_theta_squares` inverts the
squares.
"""
function thomae_theta_constants(a::Vector; squares::Bool = false, check::Bool = true)
  _check_branch_points(a)
  a = _branch_points_with_infinity(a)
  fourth_powers = _thomae_fourth_powers(a)
  squares || return fourth_powers
  return _thomae_theta_squares(a, fourth_powers; check = check)
end

@doc raw"""
    thomae_theta_constants(f::PolyRingElem; squares::Bool = false, check::Bool = true) -> Dict, Vector

The theta constants (see thomae_theta_constants(a)) of y^2 = f(x), f
squarefree of degree 2g + 1 or 2g + 2, and the branch points (the roots of f
in the order used for the labeling). Over a finite field the roots are taken
in the splitting field of f (and its quadratic extension for `squares =
true`); over other fields f must split.
"""
function thomae_theta_constants(f::PolyRingElem; squares::Bool = false, check::Bool = true)
  a = _branch_points(f)
  return thomae_theta_constants(a; squares = squares, check = check), a
end

function _branch_points(f::PolyRingElem)
  K = base_ring(f)
  @req is_squarefree(f) "f must be squarefree."
  @req degree(f) >= 5 "f must have degree at least 5."
  if K isa FqField
    d = lcm([degree(p) for (p, _) in factor(f)])
    L = _finite_field_extension(K, d)
    a = roots(L, f)
  else
    a = roots(f)
  end
  @req length(a) == degree(f) "f does not split over $(K)."
  return sort(a; by = string)
end

# The extension of degree d of the finite field K
function _finite_field_extension(K::FqField, d::Int)
  d == 1 && return K
  L, _ = finite_field(characteristic(K), absolute_degree(K) * d, "z"; cached = false)
  return L
end

# The images of the elements x in the quadratic extension of their field, and
# that field (or the field itself if all x are squares)
function _with_square_roots(x::Vector{T}) where T <: FieldElem
  K = parent(x[1])
  roots = [is_square_with_sqrt(y) for y in x]
  all(first, roots) && return [r[2] for r in roots]
  @req K isa FqField "The fourth powers of the theta constants are not squares in $(K): extend the field."
  L = _finite_field_extension(K, 2)
  embedding = embed(K, L)
  return [sqrt(embedding(y)) for y in x]
end

################################################################################
#
#  The squares
#
################################################################################

# GF(2) linear algebra on bit-packed rows (the systems for the signs are large
# and very sparse): incremental elimination with a pivot for each row
mutable struct _GF2System
  ncols::Int
  words::Int
  pivots::Dict{Int, Tuple{Vector{UInt64}, Bool}}   # pivot column => (row, rhs)
end

_GF2System(ncols::Int) = _GF2System(ncols, cld(ncols, 64), Dict{Int, Tuple{Vector{UInt64}, Bool}}())

_bit(row::Vector{UInt64}, j::Int) = (row[(j - 1) >> 6 + 1] >> ((j - 1) & 63)) & 1 == 1
_flip!(row::Vector{UInt64}, j::Int) = (row[(j - 1) >> 6 + 1] ⊻= UInt64(1) << ((j - 1) & 63); row)

function _first_bit(row::Vector{UInt64})
  for (w, x) in enumerate(row)
    iszero(x) || return 64 * (w - 1) + trailing_zeros(x) + 1
  end
  return 0
end

# Add the equation sum_{j in columns} s_j = rhs; false if it contradicts the
# previous ones
function _add_equation!(S::_GF2System, columns, rhs::Bool)
  row = zeros(UInt64, S.words)
  for j in columns
    _flip!(row, j)
  end
  while true
    j = _first_bit(row)
    j == 0 && return !rhs
    haskey(S.pivots, j) || break
    pivot_row, pivot_rhs = S.pivots[j]
    row .⊻= pivot_row
    rhs ⊻= pivot_rhs
  end
  S.pivots[_first_bit(row)] = (row, rhs)
  return true
end

# A solution (the free variables 0) by back substitution
function _solve(S::_GF2System)
  solution = falses(S.ncols)
  for j in sort(collect(keys(S.pivots)); rev = true)
    row, rhs = S.pivots[j]
    value = rhs
    for k in j+1:S.ncols
      _bit(row, k) && solution[k] && (value = !value)
    end
    solution[j] = value
  end
  return solution
end

# theta^2(S) = s_S t_S: the signs s_S from Takase's relations. Their
# solutions form an affine space of dimension 2g + 1 (the signs
# (-1)^(e + v.m), see the top of the file); relations are
# added until the rank is the number of unknowns minus 2g + 1: first those of
# _add_takase_relation! for the rotations of the sorted partition, then for random
# partitions.
function _thomae_theta_squares(a::Vector, fourth_powers::Dict; check::Bool = true)
  g = div(length(a) - 1, 2)
  eta, U = _mumford_eta_standard(g)
  sets = _thomae_sets(g)
  characteristics = [_thomae_characteristic(eta, U, S, g) for S in sets]
  index = Dict(c => k for (k, c) in enumerate(characteristics))
  roots = _with_square_roots([fourth_powers[c] for c in characteristics])
  L = parent(roots[1])
  branch_points = a
  if parent(a[1]) !== L
    embedding = embed(parent(a[1]), L)
    branch_points = [embedding(x) for x in a]
  end
  system = _GF2System(length(sets))
  target = length(sets) - (2 * g + 1)
  triples = [(k, l, m) for k in 1:2*g+1 for l in 1:2*g+1 for m in l+1:2*g+1 if k != l && k != m]
  for (k, l, m) in triples
    rest = setdiff(1:2*g+1, [k, l, m])
    for shift in 0:max(0, 2*g - 3)
      _add_takase_relation!(system, branch_points, roots, index, eta, U, g, k, l, m, circshift(rest, shift))
      length(system.pivots) == target && break
    end
    length(system.pivots) == target && break
  end
  rng = Hecke.Random.MersenneTwister(1)
  attempts = 0
  while length(system.pivots) < target
    attempts += 1
    @req attempts < 100 * length(sets) "Takase's relations do not determine the signs (rank $(length(system.pivots)) < $target)."
    k, l, m = triples[rand(rng, 1:length(triples))]
    rest = Hecke.Random.shuffle(rng, setdiff(1:2*g+1, [k, l, m]))
    _add_takase_relation!(system, branch_points, roots, index, eta, U, g, k, l, m, rest)
  end
  signs = _solve(system)
  result = Dict{NTuple{2 * g, Int}, elem_type(L)}()
  for mask in 0:4^g - 1
    result[_char_from_mask(mask, g)] = zero(L)
  end
  for (k, c) in enumerate(characteristics)
    result[c] = signs[k] ? -roots[k] : roots[k]
  end
  check && @req theta_squares_relations_hold(result) "The squares do not satisfy the quadratic relations (please report)."
  return result
end

# Takase's relation for k, l, m and the partition V = rest[1:g-1],
# W = rest[g:2g-2] as an equation for the signs
function _add_takase_relation!(system::_GF2System, a, roots, index, eta, U, g::Int, k::Int, l::Int, m::Int, rest)
  column(S) = index[_thomae_characteristic(eta, U, S, g)]
  e1 = eta[k]
  e2 = _f2(eta[k] + eta[l] + eta[m])
  exponent = sum(e1[i] * e2[g + i] for i in 1:g) + (k in U ? 0 : 1) - 1
  sign = iseven(exponent) ? 1 : -1
  quotient = divexact(a[l] - a[k], a[m] - a[k])
  V, W = rest[1:g - 1], rest[g:2*g - 2]
  columns = [column([V; k; l]), column([W; k; l]), column([V; k; m]), column([W; k; m])]
  value = sign * divexact(roots[columns[1]] * roots[columns[2]], roots[columns[3]] * roots[columns[4]])
  if value == quotient
    rhs = false
  elseif value == -quotient
    rhs = true
  else
    error("Takase's relation does not hold up to sign: the branch points do not give a curve of genus $g?")
  end
  # a column that occurs twice cancels
  odd_columns = [c for c in unique(columns) if isodd(count(==(c), columns))]
  @req _add_equation!(system, odd_columns, rhs) "Takase's relations are inconsistent."
  return system
end

################################################################################
#
#  Second order theta constants and the Rosenhain invariants
#
################################################################################

# P_a(c) = sum_b (-1)^(b.c) theta[a; b]^2 = 2^g Theta[c] Theta[c + a] with
# Theta[c] = theta[c; 0](2 tau)
function _second_order_products(thetas_sq::Dict, g::Int)
  bits = [collect(_char_from_mask(m, g))[1:g] for m in 0:2^g - 1]
  products = Dict{Tuple{Vector{Int}, Vector{Int}}, valtype(thetas_sq)}()
  for a in bits, c in bits
    products[(a, c)] = sum((isodd(sum(b .* c)) ? -1 : 1) * thetas_sq[Tuple([a; b])] for b in bits)
  end
  return products, bits
end

@doc raw"""
    second_order_theta_constants(thetas_sq::Dict) -> Vector

The second order theta constants (Theta[c](2 tau))_c, c in {0,1}^g (in the
order of the bits of c as a binary number, first entry lowest), up to a common
factor, from the squares of the theta constants by
theta[a; b]^2 = sum_c (-1)^(b.c) Theta[c] Theta[c + a]: Theta[c] is
proportional to the coefficient P_c(0) = 2^g Theta[0] Theta[c]: the theta
null point of level 2 of the Kummer variety.
"""
function second_order_theta_constants(thetas_sq::Dict)
  g = _genus_of_thetas(thetas_sq)
  products, bits = _second_order_products(thetas_sq, g)
  zero_bits = zeros(Int, g)
  @req !iszero(products[(zero_bits, zero_bits)]) "Theta[0](2 tau) vanishes."
  return [products[(c, zero_bits)] for c in bits]
end

@doc raw"""
    theta_squares_relations_hold(thetas_sq::Dict) -> Bool

Whether the squares of the theta constants satisfy the quadratic relations
P_a(c) P_a(d) = P_(c+d)(c) P_(c+d)(c+a) (all equal to 4^g Theta[c] Theta[c+a]
Theta[d] Theta[d+a], see second_order_theta_constants): a check of the signs
of the theta^2. Exact equality (for exact fields).
"""
function theta_squares_relations_hold(thetas_sq::Dict)
  g = _genus_of_thetas(thetas_sq)
  products, bits = _second_order_products(thetas_sq, g)
  for a in bits, c in bits, d in bits
    products[(a, c)] * products[(a, d)] == products[(_f2(c + d), c)] * products[(_f2(c + d), _f2(c + a))] || return false
  end
  return true
end

@doc raw"""
    rosenhain_invariants_from_theta_squares(thetas_sq::Dict) -> Vector

The Rosenhain invariants lambda_3, .., lambda_2g+1 (the curve
y^2 = x (x - 1) prod (x - lambda_l)) from the squares of the theta constants
labeled by Mumford's eta map in the standard basis (e.g. the output of
thomae_theta_constants(a; squares = true)) by Takase's formula, over any field:
the branch points (a_l - a_1) / (a_2 - a_1).
"""
function rosenhain_invariants_from_theta_squares(thetas_sq::Dict)
  g = _genus_of_thetas(thetas_sq)
  eta, U = _mumford_eta_standard(g)
  return [_takase_quotient(thetas_sq, eta, U, 1, l, 2) for l in 3:2*g+1]
end
