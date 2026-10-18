################################################################################
#
#  Hyperelliptic.jl : hyperelliptic curves of any genus
#
#  Mumford's description (Tata lectures II, IIIa.8): label the branch points
#  1, ..., 2g + 2 (2g + 2 the one at infinity), eta_S = sum_{i in S} eta_i the
#  2-torsion points (eta_{2g+2} = 0) and U the set of g + 1 branch points of
#  the Riemann constant. Then theta[eta_U + eta_S] (|S| = g + 1) are the even
#  theta constants that do not vanish.
#
#  Over the complex field (from the theta constants): the eta_i and U are
#  recovered from the pattern of the vanishing theta constants
#  (_hyperelliptic_eta), then the Rosenhain form
#  y^2 = x (x - 1) prod_l (x - lambda_l) by Takase's formula, as in genus 3 and
#  4 (_takase_quotient, ReconstructCurvesG123.jl).
#
#  Over K (from the big period matrix of the differentials x^(j-1) dx / y):
#  the gradient of an odd theta function with nonvanishing gradient is the
#  differential sum_j d_j x^(j-1) dx / y that vanishes doubly at g - 1
#  Weierstrass points, so the roots of sum_j d_j x^(j-1) are branch points;
#  together they give f up to a constant (a quadratic twist).
#
################################################################################

# The number of even theta constants that vanish for a hyperelliptic curve
_hyperelliptic_vanishing_count(g::Int) = 2^(g - 1) * (2^g + 1) - binomial(2*g + 1, g)

# The characteristic (bits) as an integer: bit i - 1 for entry i
_char_mask(c) = sum(Int(c[i]) << (i - 1) for i in eachindex(c))

# The k-element subsets of 1:n
function _subsets(n::Int, k::Int)
  result = Vector{Int}[]
  function extend!(current, start)
    length(current) == k && return push!(result, copy(current))
    for i in start:n - (k - length(current)) + 1
      push!(current, i)
      extend!(current, i + 1)
      pop!(current)
    end
  end
  extend!(Int[], 1)
  return result
end

# eta_1, ..., eta_2g+2 (bits; eta_2g+2 = 0) and U (containing 2g + 2, g + 1
# elements) from the vanishing even theta constants of a hyperelliptic curve.
#  - The sums a + b of two nonvanishing even characteristics a, b: the
#    2-torsion points eta_i + eta_j are those that occur most often (C(2g, g)/2
#    times; sums of more branch points occur less often).
#  - A star of these at one branch point (which becomes 2g + 2): e = eta_pq,
#    f0 = eta_pr, and the f = eta_ps with e + f and f + f0 of the same kind.
#  - U: the unique set (containing 2g + 2, of size g + 1) with
#    eta_U + eta_S nonvanishing for all S of size g + 1.
function _hyperelliptic_eta(g::Int, thetas, vanishing)
  zero_set = Set(_char_mask(c) for c in vanishing)
  nonvanishing = [_char_mask(c) for c in keys(thetas) if _is_even(c) && !(_char_mask(c) in zero_set)]
  counts = Dict{Int, Int}()
  for i in 1:length(nonvanishing) - 1, j in i + 1:length(nonvanishing)
    x = xor(nonvanishing[i], nonvanishing[j])
    counts[x] = get(counts, x, 0) + 1
  end
  top = maximum(values(counts))
  edges = Set(x for (x, c) in counts if c == top)
  @req length(edges) == binomial(2*g + 2, 2) "The vanishing theta constants do not have the configuration of a hyperelliptic curve."
  e = first(edges)
  adjacent = [f for f in edges if f != e && xor(e, f) in edges]
  f0 = adjacent[1]
  star = [e, f0]
  for f in adjacent
    f != f0 && xor(f, f0) in edges && xor(f, f0) != e && push!(star, f)
  end
  @req length(star) == 2*g + 1 "The vanishing theta constants do not have the configuration of a hyperelliptic curve."
  masks = [star; 0]
  eta = [collect(_char_from_mask(m, g)) for m in masks]
  nonvanishing_set = Set(nonvanishing)
  subset_masks = [reduce(xor, masks[S]) for S in _subsets(2*g + 2, g + 1)]
  for V in _subsets(2*g + 1, g)
    u = reduce(xor, masks[V]; init = 0)
    all(s -> xor(u, s) in nonvanishing_set, subset_masks) && return eta, [V; 2*g + 2]
  end
  error("The vanishing theta constants do not have the configuration of a hyperelliptic curve.")
end

# The Rosenhain form y^2 = x (x - 1) prod (x - lambda_l) over CC and the
# lambda_l
function _hyperelliptic_curve_from_thetas(g::Int, thetas, vanishing)
  eta, U = _hyperelliptic_eta(g, thetas, vanishing)
  thetas_sq = Dict(c => v^2 for (c, v) in thetas)
  lambdas = [_takase_quotient(thetas_sq, eta, U, 1, l, 2) for l in 3:2*g+1]
  CC = parent(first(values(thetas)))
  CCx, x = polynomial_ring(CC, :x; cached = false)
  return hyperelliptic_curve(x * (x - 1) * prod(x - l for l in lambdas)), lambdas
end

@doc raw"""
    reconstruct_hyperelliptic_curve(P::AcbMatrix, K = QQ; place = nothing) -> HypellCrv

The hyperelliptic curve y^2 = f(x) over K (QQ or a number field, embedded by
`place`) with big period matrix `P` (g x 2g) of the differentials
x^(j-1) dx / y, j = 1..g (e.g. big_period_matrix(riemann_surface(y^2 - f(x)))
for some model; any differentials whose canonical image is the rational normal
curve (1 : x : .. : x^(g-1)) for a function x of degree 2 over K), up to a
quadratic twist: f is monic of degree 2g + 1 or 2g + 2.

The gradients of the odd theta functions (FLINT) in the coordinates of these
differentials are polynomials whose roots are g - 1 of the branch points;
their roots are collected and identified, and the coefficients of the monic
polynomial with these roots are recognized in K.
"""
function reconstruct_hyperelliptic_curve(P::AcbMatrix, K = QQ; place = nothing)
  g = nrows(P)
  @req ncols(P) == 2*g && g >= 2 "P must be a g x 2g matrix, g >= 2."
  CC = base_ring(P)
  prec = precision(CC)
  tau = _small_period_matrix(P)
  G = _odd_theta_gradients(tau, odd_theta_characteristics(g))
  # rows: the coefficients d of the differentials sum_j d_j x^(j-1) dx / y
  D = G * _inv_precond(P[:, 1:g])
  scale = maximum(_abs64(D[i, j]) for i in 1:nrows(D), j in 1:g)
  CCx, x = polynomial_ring(CC, :x; cached = false)
  points = AcbFieldElem[]
  for r in 1:nrows(D)
    d = [D[r, j] for j in 1:g]
    size = maximum(_abs64, d)
    size < 2.0^(-prec / 4) * scale && continue          # vanishing gradient
    # a branch point at infinity lowers the degree; only full degree is used
    _abs64(d[g]) < 2.0^(-prec / 8) * size && continue
    p = sum(d[j] * x^(j - 1) for j in 1:g)
    for root in roots(p)
      any(q -> _abs64(q - root) < 2.0^(-prec / 8) * (1 + _abs64(root)), points) || push!(points, root)
    end
  end
  @req length(points) in (2*g + 1, 2*g + 2) "Found $(length(points)) branch points instead of $(2*g + 1) or $(2*g + 2): not a hyperelliptic curve with these differentials, or not enough precision."
  f = prod(x - a for a in points)
  F, _, recognize, _ = _g4_field_data(K, place, CC)
  coefficients_K = [recognize(coeff(f, k)) for k in 0:degree(f)]
  @req all(!isnothing, coefficients_K) "Could not recognize the coefficients of f in $K (more precision needed?)."
  Fx, X = polynomial_ring(F, :x; cached = false)
  return hyperelliptic_curve(sum(c * X^(k - 1) for (k, c) in enumerate(coefficients_K)))
end
