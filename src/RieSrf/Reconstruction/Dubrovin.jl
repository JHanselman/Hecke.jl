################################################################################
#
#  Dubrovin.jl : the canonical model from the Dubrovin threefold
#
#  The method of Agostini, Celik and Eken, "Numerical reconstruction of curves
#  from their Jacobians" (arXiv:2103.03138), Algorithm 1, based on
#  Agostini, Celik, Struwe and Sturmfels, "The Dubrovin threefold of an
#  algebraic curve" (arXiv:2005.08244).
#
#  For the second order theta functions th[e](z) = theta[e; 0](z, 2 tau),
#  e in {0,1}^g, the quartics
#
#     sum_e lambda_e d_U^4 th[e](0)   with   sum_e lambda_e th[e](0) = 0,
#                                            sum_e lambda_e Hess th[e](0) = 0
#
#  (a space of dimension 2^g - g(g+1)/2 - 1, Lemma 2.1) cut out the canonical
#  model of a non-hyperelliptic curve with Riemann matrix tau, in the
#  coordinates U of the normalized differentials. They come from the Hirota
#  form of the KP equation (the Dubrovin quartics with the terms in V, W, c, d
#  eliminated). The th[e] are even; with c[e, alpha] the Taylor coefficients
#  at 0 (FLINT's acb_theta_jet at 2 tau) the conditions are
#  sum_e lambda_e c[e, alpha] = 0 for |alpha| = 0 and |alpha| = 2, and the
#  quartics are sum_e lambda_e sum_{|alpha| = 4} c[e, alpha] U^alpha
#  (d_U^4 th(0) is 24 times this).
#
#  Compared with reconstruct_quadrics: only 2^g theta functions (at 2 tau,
#  jets of order 4) and linear algebra of size 2^g; no theta constants with
#  all 4^g characteristics, no signs, no Prym, no Fay relations, and the same
#  for all non-hyperelliptic curves (also trigonal curves, plane quintics and
#  curves with a vanishing theta null). The output is a set of quartics that
#  cuts out the curve, not the ideal: a small part of the quartics in the
#  ideal, without the quadrics and cubics.
#
################################################################################

# The Taylor coefficients at z = 0 of theta[e; 0](z, tau2) for all e in
# {0,1}^g (rows, in the order of Iterators.product, e[1] fastest) of the
# given degrees (columns: _exponent_vectors(g, d) for d in degrees, in this
# order). One acb_theta_jet call per characteristic.
function _second_order_theta_jets(tau2::AcbMatrix, degrees::Vector{Int})
  g = nrows(tau2)
  CC = base_ring(tau2)
  prec = precision(CC)
  order = maximum(degrees)
  n = ccall((:acb_theta_jet_nb, libflint), Int, (Int, Int), order, g)
  tuples = zeros(Int, n * g)
  GC.@preserve tuples ccall((:acb_theta_jet_tuples, libflint), Nothing, (Ptr{Int}, Int, Int),
                            pointer(tuples), order, g)
  position = Dict(tuples[g*(k-1)+1:g*k] => k for k in 1:n)
  monomials = reduce(vcat, [_exponent_vectors(g, d) for d in degrees])
  chars = [collect(e) for e in Iterators.product(ntuple(_ -> 0:1, g)...)]
  J = zero_matrix(CC, length(chars), length(monomials))
  zs = acb_vec([zero(CC) for _ in 1:g])
  jets = acb_vec(n)
  for (r, e) in enumerate(chars)
    ab = UInt(Hecke.parse_theta_characteristic([e; zeros(Int, g)]))
    ccall((:acb_theta_jet, libflint), Nothing,
          (Ptr{acb_struct}, Ptr{acb_struct}, Int, Ref{AcbMatrix}, Int, UInt, Cint, Cint, Int),
          jets, zs, 1, tau2, order, ab, 0, 0, prec)
    values = array(CC, jets, n)
    for (c, m) in enumerate(monomials)
      J[r, c] = values[position[m]]
    end
  end
  acb_vec_clear(jets, n)
  acb_vec_clear(zs, g)
  return J, monomials
end

# The Dubrovin quartics over CC in the normalized coordinates of tau (any
# Riemann matrix; FLINT reduces 2 tau itself) and the data of the
# computation: the kernel lambda (columns) and `info` (log2 of the relative
# residual of the kernel, the relative singular values of the quartics).
function _dubrovin_quartics(tau::AcbMatrix)
  g = nrows(tau)
  CC = base_ring(tau)
  J, monomials = _second_order_theta_jets(2 * tau, [0, 2, 4])
  low = 1 + binomial(g + 1, 2)                     # the columns of degree 0 and 2
  A = J[:, 1:low]
  count = 2^g - low
  @req count > 0 "No Dubrovin quartics in genus $g (2^g <= g(g + 1)/2 + 1)."
  N, _, _ = numerical_kernel(transpose(A); nullity = count)
  quartic_coefficients = transpose(N) * J[:, low+1:end]
  R, U = polynomial_ring(CC, ["u$i" for i in 1:g]; cached = false)
  quartic_monomials = monomials[low+1:end]
  quartics = [sum(quartic_coefficients[r, k] * prod(U[j]^quartic_monomials[k][j] for j in 1:g)
                  for k in eachindex(quartic_monomials)) for r in 1:count]
  info = (kernel = _log2_relative_residual(transpose(A), N),
          singular_values = _relative_singular_values64(quartic_coefficients))
  return quartics, (lambda = N, info = info)
end

@doc raw"""
    dubrovin_quartics(tau::AcbMatrix) -> Vector{MPolyRingElem}
    dubrovin_quartics(P::AcbMatrix, K = QQ; place = nothing, normalize = true, reduce_units = true,
                      numerical = false) -> Vector{MPolyRingElem}

The quartics of Agostini, Celik and Eken (arXiv:2103.03138, Algorithm 1,
from the Dubrovin threefold) that cut out the canonical model of a
non-hyperelliptic curve of genus g >= 3, from

 - its small period matrix `tau`: 2^g - g(g + 1)/2 - 1 quartics over the
   complex field, in the coordinates of the normalized differentials of
   `tau`;
 - its big period matrix `P` (g x 2g) whose rows are a basis of the
   differentials defined over K (QQ or a number field, embedded by `place`):
   the reduced echelon basis of the span of the quartics in the coordinates
   of these differentials, with coefficients in K (normalized as in
   reconstruct_quadrics); with K = nothing over the complex field, with
   `numerical = true` its matrix (`rref`, `pivots`, `monomials`, `info`).

Only the second order theta functions theta[e; 0](z, 2 tau) and their
derivatives up to order 4 at z = 0 are needed. The quartics are a small part
of the quartics in the ideal of the curve: they cut it out, but do not
generate the ideal (for that see reconstruct_curve). For a hyperelliptic
curve they do not cut out the curve.
"""
function dubrovin_quartics(tau::AcbMatrix; kw...)
  g = nrows(tau)
  ncols(tau) == 2*g && return dubrovin_quartics(tau, nothing; kw...)
  @req ncols(tau) == g && g >= 3 "tau must be a g x g matrix with g >= 3."
  return _dubrovin_quartics(tau)[1]
end

function dubrovin_quartics(P::AcbMatrix, K; place = nothing, normalize::Bool = true,
                           reduce_units::Bool = true, numerical::Bool = false)
  g = nrows(P)
  @req ncols(P) == 2*g && g >= 3 "P must be a g x 2g matrix with g >= 3."
  CC = base_ring(P)
  T, tau_red = Hecke.siegel_reduction(_small_period_matrix(P))
  quartics, data = _dubrovin_quartics(tau_red)
  # the normalized coordinates of tau_red from the differentials of P
  L = _coordinates_from_differentials(P, tau_red, T, identity_matrix(CC, g))
  Q = _substitute_coordinates(quartics, L)
  if numerical || K === nothing
    A, monomials = _coefficient_matrix(Q, 4)
    E, pivots = _numerical_rref(A)
    numerical && return (rref = E, pivots = pivots, monomials = monomials, info = data.info)
    R = parent(Q[1])
    return [sum(E[r, k] * prod(gens(R)[j]^monomials[k][j] for j in 1:g) for k in eachindex(monomials))
            for r in 1:nrows(E)]
  end
  return _recognize_forms(Q, 4, K, place; normalize, reduce_units, what = "quartic")
end
