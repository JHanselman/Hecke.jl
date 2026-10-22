################################################################################
#
#  PlaneQuinticsAndCubicThreefolds.jl : the two Pryms of a plane quintic
#
#  A smooth plane quintic C (genus 6) has the odd theta characteristic
#  kappa = O(1) with h^0 = 3 (its gradient vanishes). For a 2-torsion point
#  eta the Prym variety of the double cover is
#
#   - the Jacobian of a genus 5 curve X if kappa + eta is even (Masiewicki),
#     and then C is the discriminant of the net of quadrics through X: for
#     X = V(Q1, Q2, Q3) in P^4, C = V(det(x1 Q1 + x2 Q2 + x3 Q3))
#     (reconstruct_plane_quintic);
#   - the intermediate Jacobian of a cubic threefold Y if kappa + eta is odd
#     (Beauville); the reconstruction then finds 5 quadrics, which span the
#     partial derivatives of the cubic form of Y (Clemens-Griffiths: the
#     tangent cone of the theta divisor at its triple point is Y), so Y is
#     the cubic F with dF/dx_i in their span (reconstruct_cubic_threefold).
#
#  The reconstruction uses eta = (0..0; 1 0..0). For another eta the theta
#  constants are moved first (Igusa's transformation formula,
#  _transform_theta_constants) by a symplectic matrix that maps eta to it.
#
################################################################################

# The theta constants moved so that the Prym for eta = (0..0; 1 0..0) has
# the parity `parity` of kappa + eta (0: a Jacobian, 1: an intermediate
# Jacobian): unchanged if it already has, otherwise for the first eta that has
function _move_eta_for_parity(thetas, kappa, parity::Int)
  g = _genus_of_thetas(thetas)
  M = _eta_parity_transformation(kappa, parity, g)
  M === nothing && return thetas
  return _transform_theta_constants(thetas, M, g)
end

# A symplectic matrix that maps an eta with the parity `parity` of
# kappa + eta to eta = (0..0; 1 0..0), or nothing if the standard eta has it
function _eta_parity_transformation(kappa, parity::Int, g::Int)
  standard = [i == g + 1 ? 1 : 0 for i in 1:2*g]
  parity_of(eta) = _is_even(_f2(collect(kappa) .+ eta)) ? 0 : 1
  parity_of(standard) == parity && return nothing
  for mask in 1:4^g - 1
    eta = collect(_char_from_mask(mask, g))
    parity_of(eta) == parity && return _eta_to_standard(eta, g)
  end
  error("No 2-torsion point with the required parity.")
end

# The determinant of a square matrix of polynomials (Laplace expansion along
# the first row; exact in the ring operations, no division)
function _laplace_determinant(M::Matrix)
  n = size(M, 1)
  n == 1 && return M[1, 1]
  result = zero(M[1, 1])
  for j in 1:n
    iszero(M[1, j]) && continue
    minor = M[2:n, [k for k in 1:n if k != j]]
    result += (isodd(j) ? 1 : -1) * M[1, j] * _laplace_determinant(minor)
  end
  return result
end

# The symmetric matrix S with q = x^T S x of a quadric q
function _symmetric_matrix_of_quadric(q)
  n = nvars(parent(q))
  CC = base_ring(parent(q))
  half = inv(CC(2))
  S = Matrix{elem_type(CC)}(undef, n, n)
  for i in 1:n, j in 1:n
    e = zeros(Int, n)
    e[i] += 1
    e[j] += 1
    S[i, j] = i == j ? coeff(q, e) : half * coeff(q, e)
  end
  return S
end

# Masiewicki: the plane quintic from the theta constants of genus 6 and its
# kappa
function _plane_quintic_from_thetas(thetas, kappa; sign_data = nothing, kw...)
  moved = _move_eta_for_parity(thetas, kappa, 0)
  P = prym_quadrics(moved; prym_sign_data = sign_data, strict = true)
  @req length(P.quadrics) == 3 "The Prym is not the Jacobian of a genus 5 curve."
  CC = base_ring(parent(P.quadrics[1]))
  R, t = polynomial_ring(CC, [:x, :y, :z]; cached = false)
  S = [_symmetric_matrix_of_quadric(q) for q in P.quadrics]
  net = [sum(t[k] * S[k][i, j] for k in 1:3) for i in 1:5, j in 1:5]
  quintic = _laplace_determinant(net)
  largest = maximum(_abs64, coefficients(quintic))
  return inv(CC(largest)) * quintic
end

@doc raw"""
    reconstruct_plane_quintic(tau::AcbMatrix; kw...) -> MPolyRingElem
    reconstruct_plane_quintic(thetas::AbstractDict; kw...) -> MPolyRingElem

A plane quintic (over the complex field, in coordinates determined up to
PGL_3) with small period matrix `tau` (6 x 6) or theta constants `thetas`,
by Masiewicki's construction: the Prym of a 2-torsion point eta with
kappa + eta even is the Jacobian of a genus 5 curve X = V(Q1, Q2, Q3), and the
curve is det(x Q1 + y Q2 + z Q3) = 0. Needs the sign data of genus 5 and 4
(`sign_data`: genus 5). reconstruct_curve does this for plane quintics.
"""
function reconstruct_plane_quintic(tau::AcbMatrix; kw...)
  @req nrows(tau) == ncols(tau) == 6 "tau must be a 6 x 6 matrix."
  thetas, _, _ = _reduced_theta_constants(tau)
  return reconstruct_plane_quintic(thetas; kw...)
end

function reconstruct_plane_quintic(thetas::AbstractDict; fay_relations = nothing, kw...)
  @req _genus_of_thetas(thetas) == 6 "The theta constants must be of genus 6."
  K, _ = odd_theta_gradient_kernel(6, thetas; relations = fay_relations)
  kappa = _vanishing_gradient_characteristic(6, K)
  @req kappa !== nothing "No odd theta function has a vanishing gradient: not a plane quintic."
  return _plane_quintic_from_thetas(thetas, kappa; kw...)
end

################################################################################
#
#  Cubic threefolds
#
################################################################################

# The coefficient vector (monomials e2) of dF/dx_i for the cubic with
# coefficient vector f (monomials e3), as a linear map: a matrix over k
function _derivative_matrix(k, n::Int, i::Int, e3, e2)
  position = Dict(e => r for (r, e) in enumerate(e2))
  D = zero_matrix(k, length(e2), length(e3))
  for (s, e) in enumerate(e3)
    e[i] == 0 && continue
    d = copy(e)
    d[i] -= 1
    D[position[d], s] = e[i]
  end
  return D
end

# The cubic F whose partial derivatives span the space of the quadrics: the
# kernel of (N^T D_i)_i, N a basis of the linear forms on the quadratic forms
# that vanish on the quadrics. Over the complex field (numerical kernel) or
# over a field (exact).
function _cubic_from_polar_quadrics(quadrics)
  R = parent(quadrics[1])
  k = base_ring(R)
  n = nvars(R)
  e2 = _exponent_vectors(n, 2)
  e3 = _exponent_vectors(n, 3)
  A = matrix(k, length(quadrics), length(e2), [coeff(q, e) for q in quadrics for e in e2])
  exact = !(k isa AcbField)
  N = exact ? kernel(A; side = :right) : numerical_kernel(A)[1]
  system = reduce(vcat, [transpose(N) * _derivative_matrix(k, n, i, e3, e2) for i in 1:n])
  F = exact ? kernel(system; side = :right) : numerical_kernel(system)[1]
  @req ncols(F) == 1 "The quadrics are not the partial derivatives of a cubic ($(ncols(F)) solutions)."
  x = gens(R)
  return sum(F[s, 1] * prod(x[j]^e3[s][j] for j in 1:n) for s in eachindex(e3))
end

@doc raw"""
    reconstruct_cubic_threefold(tau::AcbMatrix; kw...) -> MPolyRingElem
    reconstruct_cubic_threefold(thetas::AbstractDict; kw...) -> MPolyRingElem
    reconstruct_cubic_threefold(P::AcbMatrix, K; place = nothing, kw...) -> MPolyRingElem

The cubic threefold Y (a cubic form in 5 variables) from

 - the small period matrix `tau` (5 x 5) or the theta constants (genus 5) of
   its intermediate Jacobian, over the complex field (in coordinates
   determined up to a linear change);
 - the small period matrix (6 x 6) or theta constants (genus 6) of a plane
   quintic C: Y is then the cubic of the Prym of C for a 2-torsion point eta
   with kappa + eta odd (Beauville);
 - the big period matrix `P` (5 x 10) of the intermediate Jacobian for a
   basis of its differentials defined over K: the cubic over K, in these
   coordinates.

The reconstruction finds the 5 quadrics through the image of the gradients
(reconstruct_quadrics_from_thetas with quadric_count = 5); Y is the cubic
whose partial derivatives span them. Keywords: those of
reconstruct_quadrics_from_thetas (for a plane quintic `prym_sign_data`
(genus 5) and `sign_data` (genus 4)).
"""
function reconstruct_cubic_threefold(tau::AcbMatrix; kw...)
  @req nrows(tau) == ncols(tau) "tau must be a square matrix (or pass a field for a big period matrix)."
  thetas, _, _ = _reduced_theta_constants(tau)
  return reconstruct_cubic_threefold(thetas; kw...)
end

function reconstruct_cubic_threefold(thetas::AbstractDict; fay_relations = nothing, kw...)
  g = _genus_of_thetas(thetas)
  @req g in (5, 6) "The theta constants must be of genus 5 (an intermediate Jacobian) or 6 (a plane quintic)."
  if g == 5
    quadrics = reconstruct_quadrics_from_thetas(5, thetas; quadric_count = 5, fay_relations, kw...).quadrics
  else
    K, _ = odd_theta_gradient_kernel(6, thetas; relations = fay_relations)
    kappa = _vanishing_gradient_characteristic(6, K)
    @req kappa !== nothing "No odd theta function has a vanishing gradient: not a plane quintic."
    moved = _move_eta_for_parity(thetas, kappa, 1)
    quadrics = prym_quadrics(moved; quadric_count = 5, strict = true, kw...).quadrics
  end
  return _cubic_from_polar_quadrics(quadrics)
end

function reconstruct_cubic_threefold(P::AcbMatrix, K; place = nothing, normalize::Bool = true,
                                     reduce_units::Bool = true, kw...)
  @req nrows(P) == 5 && ncols(P) == 10 "P must be a 5 x 10 matrix."
  quadrics = reconstruct_quadrics(P, K; place, normalize = false, quadric_count = 5, kw...)
  F = _cubic_from_polar_quadrics(quadrics)
  return normalize ? _normalize_model(F; reduce_units) : F
end
