################################################################################
#
#  Quadrics.jl : the quadrics through the canonical model (genus g >= 5)
#
#  The generalization of the genus 4 method (ReconstructG4.jl) to g >= 5,
#  with the Prym of eta = (0..0; 1 0..0) and without tables:
#
#   1. The gradients l_kappa of the odd theta functions at 0, up to a common
#      linear map: the kernel K of Fay's relations (FayRelations.jl). Its
#      rows are the tangent hyperplanes of the canonical model.
#   2. The same for the Prym (genus g - 1), whose theta constants come from
#      Schottky-Jung with the signs of Riemann's relations (prym_thetas,
#      SignCorrection.jl): the rows m_d of K_P.
#   3. A linear relation sum_d c_d m_d^2 = 0 between the squares gives the
#      quadric sum_d c_d l_kappa(d) l_kappa(d)+eta through the canonical model
#      (kappa(d) = (0 d1; 0 d2)). These span the (g - 2)(g - 3)/2 quadrics
#      that contain it.
#
#  The quadrics are in the coordinates of K. With the big period matrix and
#  the gradients of the theta functions at 0 (FLINT) they are moved to the
#  coordinates of the differentials of the period matrix, where they are
#  defined over the field of the curve and recognized there.
#
#  Theta constants: those of FLINT (Hecke.thetas) for the curve; only the
#  Schottky-Jung constants of the Prym get their signs from Riemann's
#  relations.
#
#  Entry points: reconstruct_quadrics, prym_quadrics.
#
################################################################################

# The genus of a dictionary of theta constants (keys of 2g bits)
_genus_of_thetas(thetas) = div(length(first(keys(thetas))), 2)

# All theta constants of tau by FLINT (tau is Siegel reduced first: T, the
# transformation, and the reduced tau are returned too). For g >= 5 the basis
# is changed further if a vanishing theta null would make a theta constant of
# the Prym vanish (_prym_safe_transformations).
function _reduced_theta_constants(tau::AcbMatrix)
  T, tau_red = Hecke.siegel_reduction(tau)
  thetas = theta_constants(tau_red)
  g = nrows(tau)
  g >= 5 || return thetas, tau_red, T
  prec = precision(base_ring(tau))
  vanishing = _vanishing_even_theta_constants(thetas, prec)
  _vanishing_outside_prym(vanishing) && return thetas, tau_red, T
  for M in _prym_safe_transformations(vanishing, g)
    thetas2, tau2, T2 = _moved_basis(M, thetas, tau_red, T)
    _vanishing_outside_prym(_vanishing_even_theta_constants(thetas2, prec)) && return thetas2, tau2, T2
  end
  error("No symplectic basis in which the vanishing theta constants avoid the Prym.")
end

# For g = 6 the curve may be a plane quintic (kappa: the odd characteristic
# with vanishing gradient); the Prym of eta = (0..0; 1 0..0) is then a
# Jacobian only if kappa + eta is even, otherwise the basis is changed
# (_moved_basis, keeping tau and T consistent). Returns the basis and the
# gradient kernel of the curve if it is still valid (else nothing).
function _plane_quintic_safe_basis(g::Int, thetas, tau, T; rhos = nothing, fay_relations = nothing, kw...)
  basis = (thetas = thetas, tau = tau, transform = T)
  g == 6 || return basis, nothing
  gradient_kernel = odd_theta_gradient_kernel(g, thetas; rhos = rhos, relations = fay_relations)
  kappa = _vanishing_gradient_characteristic(g, gradient_kernel[1])
  M = kappa === nothing ? nothing : _eta_parity_transformation(kappa, 0, g)
  M === nothing && return basis, gradient_kernel
  thetas2, tau2, T2 = _moved_basis(M, thetas, tau, T)
  return (thetas = thetas2, tau = tau2, transform = T2), nothing
end

# The theta constants in the basis changed by the symplectic matrix M
# (characteristics as in _igusa_action), with tau and the transformation T
# (M tau = Hecke.siegel_transform(M, tau); theta constants by FLINT) if tau is
# known, otherwise by Igusa's transformation formula (up to a common factor).
function _moved_basis(M::Matrix{Int}, thetas, tau, T)
  tau === nothing && return _transform_theta_constants(thetas, M, _genus_of_thetas(thetas)), nothing, nothing
  MZ = matrix(ZZ, M)
  tau2 = Hecke.siegel_transform(MZ, tau)
  tau2 = (tau2 + transpose(tau2)) * inv(base_ring(tau2)(2))
  return theta_constants(tau2), tau2, MZ * T
end

# The theta constants of the Prym for eta = (0..0; 1 0..0) are the products
# theta[0 a; 0 b] theta[0 a; 1 b] (prym_thetas): a vanishing even
# characteristic of the curve makes one of them vanish unless its first bit
# is 1. For hyperelliptic curves (where this cannot be avoided) nothing is
# moved.
function _vanishing_outside_prym(vanishing)
  isempty(vanishing) && return true
  g = div(length(first(vanishing)), 2)
  length(vanishing) == _hyperelliptic_vanishing_count(g) && return true
  return all(c -> c[1] == 1, vanishing)
end

# Candidate symplectic matrices (single transvections, then products of two)
# that move all characteristics in `vanishing` to ones with first bit 1
function _prym_safe_transformations(vanishing, g::Int)
  moves(M) = _vanishing_outside_prym([Tuple(_f2(_igusa_action(M, collect(c), g)[1])) for c in vanishing])
  transvections = [_integral_transvection(collect(_char_from_mask(mask, g)), g) for mask in 1:4^g - 1]
  return Iterators.flatten((Iterators.filter(moves, transvections),
                            Iterators.filter(moves, (s * t for s in transvections[1:min(end, 64)] for t in transvections))))
end

# The same on the theta constants only (Igusa's transformation formula, up to
# a common factor)
function _theta_constants_avoiding_prym(thetas)
  g = _genus_of_thetas(thetas)
  g >= 5 || return thetas
  prec = precision(parent(first(values(thetas))))
  vanishing = _vanishing_even_theta_constants(thetas, prec)
  _vanishing_outside_prym(vanishing) && return thetas
  return _transform_theta_constants(thetas, first(_prym_safe_transformations(vanishing, g)), g)
end

################################################################################
#
#  From the gradients to the quadrics
#
################################################################################

# The quadrics from the gradients (rows of K) and those of the Prym (rows of
# K_prym): relations c between the squares m_d^2 give sum_d c_d l l'. The
# symmetric matrices are stored by their entries (i, j), i >= j. The number
# of quadrics is (g - 2)(g - 3)/2 for a Jacobian, or `quadric_count` (e.g. 5
# for the intermediate Jacobian of a cubic threefold). `info`: log2 residuals
# (about -precision if the relations hold) and the singular values of the
# relation matrix (relative, Float64: `quadric_count` of them are not small).
function _quadrics_from_gradients(g::Int, K::AcbMatrix, K_prym::AcbMatrix; strict::Bool = true,
                                  quadric_count::Union{Int, Nothing} = nothing)
  CC = base_ring(K)
  prec = precision(CC)
  lower(n) = [(i, j) for j in 1:n for i in j:n]
  index_pairs = lift_prym_indices(g)
  n = length(index_pairs)
  # rows: the symmetric products l_kappa l_{kappa + eta} and the squares m_d^2
  products = zero_matrix(CC, n, length(lower(g)))
  squares = zero_matrix(CC, n, length(lower(g - 1)))
  for (d, (i1, i2)) in enumerate(index_pairs)
    for (k, (a, b)) in enumerate(lower(g))
      products[d, k] = K[i1, a] * K[i2, b] + K[i2, a] * K[i1, b]
    end
    for (k, (a, b)) in enumerate(lower(g - 1))
      squares[d, k] = K_prym[d, a] * K_prym[d, b]
    end
  end
  # the relations between the squares (these span all quadrics in g - 1 variables)
  O = numerical_kernel(transpose(squares); nullity = n - length(lower(g - 1)))[1]
  q_relations = _log2_relative_residual(transpose(squares), O)
  @req !strict || q_relations < -prec / 4 "The squares of the Prym gradients do not span the quadrics (log2 residual $q_relations)."
  relation_matrix = transpose(O) * products
  e = quadric_count === nothing ? div((g - 2) * (g - 3), 2) : quadric_count
  data = _numerical_kernel_data(relation_matrix; nullity = length(lower(g)) - e)
  q_quadrics = _log2_relative_residual(relation_matrix, data.kernel)
  @req !strict || q_quadrics < -prec / 4 "The relations do not give $e quadrics (log2 residual $q_quadrics); wrong signs of the Prym theta constants, or a non-generic curve?"
  R, x = polynomial_ring(CC, ["x$i" for i in 1:g]; cached = false)
  half = inv(CC(2))
  quadrics = [sum((a == b ? half : one(CC)) * relation_matrix[r, k] * x[a] * x[b] for (k, (a, b)) in enumerate(lower(g)))
              for r in data.pivot_rows]
  info = (relations = q_relations, quadrics = q_quadrics,
          quadric_singular_values = _relative_singular_values64(relation_matrix))
  return quadrics, info
end

# The singular values of the rows of A (each scaled to norm 1), Float64,
# relative to the largest, decreasing
function _relative_singular_values64(A::AcbMatrix)
  rows = Matrix{ComplexF64}(undef, nrows(A), ncols(A))
  for i in 1:nrows(A)
    row = [_c64(A[i, j]) for j in 1:ncols(A)]
    m = maximum(abs, row)
    rows[i, :] = m > 0 ? row ./ m : row
  end
  s = LinearAlgebra.svdvals(rows)
  return s ./ s[1]
end

@doc raw"""
    reconstruct_quadrics_from_thetas(g, thetas; sign_data = nothing, rhos = nothing, prym_rhos = nothing,
                                     fay_relations = nothing, prym_fay_relations = nothing,
                                     sign_fallback = true, strict = true, quadric_count = nothing)
        -> NamedTuple

The quadrics through the canonical model from the theta constants `thetas`
of genus g >= 5 (all characteristics, with signs, e.g. Hecke.thetas), with
the data of the computation: `quadrics` (over the complex field, in the
coordinates of `gradients`), `gradients` (the kernel of Fay's relations,
rows: the odd characteristics), `prym_gradients`, `prym_thetas` (with
corrected signs) and `info` (log2 residuals and singular values, see
_quadrics_from_gradients).

`sign_data`: the sign data of genus g - 1 (loaded pairs or a file; default:
the stored ones); `fay_relations`, `prym_fay_relations`: see
odd_theta_gradient_kernel; `strict = false` returns the quadrics also when
the residuals are not small (e.g. to study theta constants that do not come
from a Jacobian); `quadric_count`: the number of quadrics to return instead
of (g - 2)(g - 3)/2 (5 for the intermediate Jacobian of a cubic threefold).
"""
function reconstruct_quadrics_from_thetas(g::Int, thetas; sign_data = nothing, rhos = nothing,
                                          prym_rhos = nothing, fay_relations = nothing,
                                          prym_fay_relations = nothing, sign_fallback::Bool = true,
                                          strict::Bool = true, quadric_count::Union{Int, Nothing} = nothing,
                                          gradient_kernel = nothing)
  @req g >= 5 "Only for g >= 5."
  thetas_prym = prym_thetas(g, thetas)
  _, sufficient = correct_signs_with_data!(thetas_prym, g - 1, _loaded_sign_data(sign_data, g - 1);
                                           fallback = sign_fallback)
  # gradient_kernel: (K, log2 residual) of these theta constants, if known
  K, q_K = gradient_kernel === nothing ? odd_theta_gradient_kernel(g, thetas; rhos = rhos, relations = fay_relations) :
                                         gradient_kernel
  K_prym, q_K_prym = odd_theta_gradient_kernel(g - 1, thetas_prym; rhos = prym_rhos, relations = prym_fay_relations)
  quadrics, q = _quadrics_from_gradients(g, K, K_prym; strict = strict, quadric_count = quadric_count)
  info = merge((gradients = q_K, prym_gradients = q_K_prym, sign_data_sufficed = sufficient), q)
  return (quadrics = quadrics, gradients = K, prym_gradients = K_prym, prym_thetas = thetas_prym, info = info)
end

################################################################################
#
#  The coordinates of the differentials
#
################################################################################

# The gradients at z = 0 of the theta functions of the characteristics
# `chars` (FLINT's acb_theta_jet: for a few characteristics one at a time,
# otherwise all at once), as a matrix (rows: the characteristics)
function _odd_theta_gradients(tau::AcbMatrix, chars)
  g = nrows(tau)
  CC = base_ring(tau)
  G = zero_matrix(CC, length(chars), g)
  if length(chars) > 4*g
    # many characteristics: all at once (one acb_theta_jet call for all)
    jets = Hecke.theta_jets([zero(CC) for _ in 1:g], tau, 1)
    unit(i) = g == 1 ? 1 : ntuple(j -> j == i ? 1 : 0, g)
    for (r, c) in enumerate(chars), i in 1:g
      G[r, i] = jets[Tuple(c)][unit(i)]
    end
    return G
  end
  prec = precision(CC)
  n = ccall((:acb_theta_jet_nb, libflint), Int, (Int, Int), 1, g)
  tuples = zeros(Int, n * g)
  GC.@preserve tuples ccall((:acb_theta_jet_tuples, libflint), Nothing, (Ptr{Int}, Int, Int),
                            pointer(tuples), 1, g)
  # the position of the derivative in z_i among the jets
  position = [findfirst(k -> tuples[g*(k-1)+1:g*k] == [j == i ? 1 : 0 for j in 1:g], 1:n) for i in 1:g]
  zs = acb_vec([zero(CC) for _ in 1:g])
  jets = acb_vec(n)
  for (r, c) in enumerate(chars)
    ab = UInt(Hecke.parse_theta_characteristic(collect(c)))
    ccall((:acb_theta_jet, libflint), Nothing,
          (Ptr{acb_struct}, Ptr{acb_struct}, Int, Ref{AcbMatrix}, Int, UInt, Cint, Cint, Int),
          jets, zs, 1, tau, 1, ab, 0, 0, prec)
    values = array(CC, jets, n)
    for i in 1:g
      G[r, i] = values[position[i]]
    end
  end
  acb_vec_clear(jets, n)
  acb_vec_clear(zs, g)
  return G
end

# B with K = G B, G the gradients of the odd theta functions at 0 (rows), and
# log2 of the relative residual of G B - K on the midpoints: the coordinates
# x of the quadrics are B^-1 z (z: the normalized differentials). Only the
# gradients of g well conditioned rows of K (and `checks` more, the largest
# rows of K, for the residual) are computed.
function _gradient_coordinates(tau::AcbMatrix, K::AcbMatrix; checks::Int = 3)
  g = nrows(tau)
  odds = odd_theta_characteristics(g)
  rows = _numerical_kernel_data(K; nullity = 0).pivot_rows
  sizes = [maximum(_abs64(K[r, i]) for i in 1:g) for r in 1:nrows(K)]
  extra = first(sort(setdiff(1:nrows(K), rows); by = r -> -sizes[r]), checks)
  used = [rows; extra]
  G = _odd_theta_gradients(tau, odds[used])
  Ku = matrix(base_ring(K), length(used), g, [K[r, i] for r in used for i in 1:g])
  B = _solve_precond(G[1:g, :], Ku[1:g, :])
  difference = map_entries(_acb_mid, G) * map_entries(_acb_mid, B) - map_entries(_acb_mid, Ku)
  scale = maximum(_abs64(Ku[i, j]) for i in 1:nrows(Ku), j in 1:g)
  residual = maximum(_abs64(difference[i, j]) for i in 1:nrows(Ku), j in 1:g)
  return B, _safe_log2(residual / scale)
end

# x = L y: the coordinates x of the quadrics from the coordinates y of the
# differentials of the big period matrix P = [P_A P_B]: z = P_A'^-1 y
# (normalized differentials for tau' = T(tau), P' = P [D^T B^T; C^T A^T]) and
# x = B^-1 z (K = G B).
function _coordinates_from_differentials(P::AcbMatrix, tau_red::AcbMatrix, T::ZZMatrix, B::AcbMatrix)
  g = nrows(tau_red)
  CC = base_ring(tau_red)
  Tc = change_base_ring(CC, T)
  C, D = Tc[g+1:2*g, 1:g], Tc[g+1:2*g, g+1:2*g]
  PA = P[:, 1:g] * transpose(D) + P[:, g+1:2*g] * transpose(C)
  return _inv_precond(B) * _inv_precond(PA)
end

# The small period matrix of the big period matrix P = [P_A P_B] (symmetrized)
function _small_period_matrix(P::AcbMatrix)
  g = nrows(P)
  @req ncols(P) == 2*g "The big period matrix must be a g x 2g matrix."
  tau = _solve_precond(P[:, 1:g], P[:, g+1:2*g])
  return (tau + transpose(tau)) * inv(base_ring(P)(2))
end

# The forms (polynomials over CC) after the substitution x = L y
function _substitute_coordinates(forms, L::AcbMatrix)
  g = nrows(L)
  ys = gens(parent(forms[1]))
  xy = [sum(L[i, j] * ys[j] for j in 1:g) for i in 1:g]
  return [evaluate(q, xy) for q in forms]
end

# The reduced row echelon form of A (full row rank): the pivot columns from
# elimination on the midpoints (an entry below 2^(-prec/3) of the largest is
# zero), then A[:, pivots]^-1 A in ball arithmetic.
function _numerical_rref(A::AcbMatrix)
  CC = base_ring(A)
  m, n = nrows(A), ncols(A)
  B = map_entries(_acb_mid, A)
  threshold = 2.0^(-precision(CC) / 3) * maximum(_abs64(B[i, j]) for i in 1:m, j in 1:n)
  pivots = Int[]
  r = 0
  for c in 1:n
    r == m && break
    i = r + argmax([_abs64(B[l, c]) for l in r+1:m])
    _abs64(B[i, c]) < threshold && continue
    r += 1
    B = swap_rows(B, r, i)
    for l in r+1:m
      f = _acb_mid(B[l, c] / B[r, c])
      for j in c:n
        B[l, j] = _acb_mid(B[l, j] - f * B[r, j])
      end
    end
    push!(pivots, c)
  end
  @req r == m "The quadrics are not linearly independent."
  P = matrix(CC, m, m, [A[i, c] for i in 1:m for c in pivots])
  return _solve_precond(P, A), pivots
end

# The coefficient matrix of homogeneous forms of degree d in n variables
# (columns: _exponent_vectors(n, d))
function _coefficient_matrix(forms, d::Int)
  n = nvars(parent(forms[1]))
  monomials = _exponent_vectors(n, d)
  CC = base_ring(parent(forms[1]))
  return matrix(CC, length(forms), length(monomials), [coeff(q, e) for q in forms for e in monomials]), monomials
end

# The echelon basis of the span of the forms (over the complex field) with its
# coefficients recognized in K (embedded by `place`), normalized
# (_normalize_model); an error tells how many bits were left if the
# recognition fails.
function _recognize_forms(forms, d::Int, K, place; normalize::Bool = true, reduce_units::Bool = true,
                          what::AbstractString = "form")
  A, monomials = _coefficient_matrix(forms, d)
  E, pivots = _numerical_rref(A)
  CC = base_ring(A)
  F, _, recognize, _ = _g4_field_data(K, place, CC)
  n = length(monomials[1])
  S, X = polynomial_ring(F, ["x$i" for i in 1:n]; cached = false)
  result = elem_type(S)[]
  for r in 1:nrows(E)
    cs = [c in pivots ? (c == pivots[r] ? one(F) : zero(F)) : recognize(E[r, c]) for c in 1:ncols(E)]
    if any(isnothing, cs)
      failed = [c for c in 1:ncols(E) if cs[c] === nothing]
      bits = minimum(-_log2_relative_radius(E[r, c]) for c in failed)
      error("Could not recognize $(length(failed)) of the coefficients of $what $r in $K: they are " *
            "known to only about $(round(bits, digits = 1)) bits. More precision needed? " *
            "First unrecognized coefficient: $(E[r, failed[1]])")
    end
    q = sum(cs[k] * prod(X[j]^monomials[k][j] for j in 1:n) for k in eachindex(monomials))
    push!(result, normalize ? _normalize_model(q; reduce_units) : q)
  end
  return result
end

################################################################################
#
#  User facing
#
################################################################################

# The quadrics over CC of the curve with small period matrix tau, the data
# of the computation and, with `coordinates`, B (see _gradient_coordinates)
function _quadrics_data(tau::AcbMatrix; coordinates::Bool = false, kw...)
  g = nrows(tau)
  @req ncols(tau) == g && g >= 5 "tau must be a g x g matrix with g >= 5."
  thetas, tau_red, T = _reduced_theta_constants(tau)
  basis, gradient_kernel = _plane_quintic_safe_basis(g, thetas, tau_red, T; kw...)
  thetas, tau_red, T = basis
  vanishing = _vanishing_even_theta_constants(thetas, precision(base_ring(tau)))
  # vanishing theta nulls carry no sign and are skipped by the sign correction;
  # a hyperelliptic curve is not cut out by quadrics
  @req length(vanishing) != _hyperelliptic_vanishing_count(g) "The curve is hyperelliptic: its canonical image is not cut out by quadrics (see reconstruct_hyperelliptic_curve)."
  data = reconstruct_quadrics_from_thetas(g, thetas; gradient_kernel, kw...)
  B, q_B = coordinates ? _gradient_coordinates(tau_red, data.gradients) : (nothing, NaN)
  return merge(data, (thetas = thetas, tau = tau_red, transform = T, coordinates = B,
                      info = merge(data.info, (coordinates = q_B,))))
end

@doc raw"""
    reconstruct_quadrics(tau::AcbMatrix; kw...) -> Vector{MPolyRingElem}
    reconstruct_quadrics(thetas::AbstractDict; kw...) -> Vector{MPolyRingElem}
    reconstruct_quadrics(P::AcbMatrix, K = QQ; place = nothing, normalize = true, reduce_units = true,
                         numerical = false, kw...) -> Vector{MPolyRingElem}

The quadrics through the canonical model of a curve of genus g >= 5 that is
neither hyperelliptic nor trigonal nor a plane quintic, from

 - its small period matrix `tau` (g x g) or its theta constants `thetas` (a
   dictionary as returned by Hecke.thetas): (g - 2)(g - 3)/2 quadrics over
   the complex field, in coordinates that are determined only up to a linear
   change (those of the gradients of the odd theta functions);
 - its big period matrix `P` (g x 2g) whose rows are a basis of the
   differentials defined over K (QQ or a number field, embedded by `place`),
   e.g. `big_period_matrix(RS)` for a curve over K: the quadrics in the
   coordinates of these differentials, the reduced echelon basis of their
   span with coefficients in K (with `normalize`, integral and primitive as
   in reconstruct_rational_curve_g4). With `numerical = true` the echelon form
   over the complex field, without recognition.

The theta constants of the curve are those of FLINT; only the Schottky-Jung
theta constants of the Prym get signs from Riemann's relations (the sign
data of genus g - 1, stored for g <= 8). Keywords: `sign_data`,
`fay_relations`, `prym_fay_relations`, `strict` (see
reconstruct_quadrics_from_thetas). For curves of any type use
reconstruct_curve.
"""
function reconstruct_quadrics(tau::AcbMatrix; kw...)
  nrows(tau) == ncols(tau) && return _quadrics_data(tau; kw...).quadrics
  return reconstruct_quadrics(tau, nothing; kw...)
end

function reconstruct_quadrics(thetas::AbstractDict; kw...)
  g = _genus_of_thetas(thetas)
  basis, gradient_kernel = _plane_quintic_safe_basis(g, _theta_constants_avoiding_prym(thetas), nothing, nothing; kw...)
  return reconstruct_quadrics_from_thetas(g, basis.thetas; gradient_kernel, kw...).quadrics
end

function reconstruct_quadrics(P::AcbMatrix, K; place = nothing, normalize::Bool = true,
                              reduce_units::Bool = true, numerical::Bool = false, kw...)
  g = nrows(P)
  @req ncols(P) == 2*g "P must be a g x 2g matrix."
  data = _quadrics_data(_small_period_matrix(P); coordinates = true, kw...)
  @req data.info.coordinates < -precision(base_ring(P)) / 4 "The gradient kernel is not a linear image of the theta gradients (log2 residual $(data.info.coordinates))."
  CC = base_ring(data.tau)
  L = _coordinates_from_differentials(change_base_ring(CC, P), data.tau, data.transform, data.coordinates)
  Q = _substitute_coordinates(data.quadrics, L)
  if numerical || K === nothing
    A, monomials = _coefficient_matrix(Q, 2)
    E, pivots = _numerical_rref(A)
    numerical && return (rref = E, pivots = pivots, monomials = monomials, info = data.info)
    R = parent(Q[1])
    return [sum(E[r, k] * prod(gens(R)[j]^monomials[k][j] for j in 1:g) for k in eachindex(monomials)) for r in 1:nrows(E)]
  end
  return _recognize_forms(Q, 2, K, place; normalize, reduce_units, what = "quadric")
end

@doc raw"""
    prym_quadrics(tau::AcbMatrix; quadric_count = nothing, strict = false, kw...) -> NamedTuple
    prym_quadrics(thetas::AbstractDict; kw...) -> NamedTuple

The reconstruction applied to the Prym variety of a curve of genus G >= 6 for
eta = (0..0; 1 0..0): its theta constants by Schottky-Jung (signs by
Riemann's relations, sign data of genus G - 1), then
reconstruct_quadrics_from_thetas for genus G - 1 (whose Prym needs the sign
data of genus G - 2). If the Prym is the Jacobian of a curve X, the quadrics
cut out the canonical model of X; for a plane quintic (G = 6) with
kappa + eta odd the Prym is the intermediate Jacobian of a cubic threefold
and there are 5 quadrics (`quadric_count = 5`, see
reconstruct_cubic_threefold). Keywords: `prym_sign_data` (genus G - 1),
`sign_data` (genus G - 2) and those of reconstruct_quadrics_from_thetas.
Returns that result together with `thetas` (of the Prym) and
`curve_thetas`.
"""
function prym_quadrics(tau::AcbMatrix; kw...)
  @req nrows(tau) == ncols(tau) "tau must be a square matrix."
  thetas, _, _ = _reduced_theta_constants(tau)
  return prym_quadrics(thetas; kw...)
end

function prym_quadrics(thetas::AbstractDict; prym_sign_data = nothing, strict::Bool = false, kw...)
  G = _genus_of_thetas(thetas)
  @req G >= 6 "The curve must have genus G >= 6 (a Prym of dimension >= 5)."
  thetas_P = prym_thetas(G, thetas)
  _, sufficient = correct_signs_with_data!(thetas_P, G - 1, _loaded_sign_data(prym_sign_data, G - 1))
  vanishing = _vanishing_even_theta_constants(thetas_P, precision(parent(first(values(thetas)))))
  @req isempty(vanishing) "$(length(vanishing)) even theta constants of the Prym vanish."
  result = reconstruct_quadrics_from_thetas(G - 1, thetas_P; strict = strict, kw...)
  return merge(result, (thetas = thetas_P, curve_thetas = thetas,
                        info = merge(result.info, (prym_sign_data_sufficed = sufficient,))))
end
