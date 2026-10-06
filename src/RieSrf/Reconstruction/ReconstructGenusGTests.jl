################################################################################
#
#  ReconstructGenusGTests.jl : tests of the genus g reconstruction on random
#  generic curves with known canonical model, and the curves for g = 7..10
#
#  Development code: load in Main after ReconstructGenusG.jl.
#
#  canonical_test_curve(g): a random plane curve of the minimal degree d of
#  the generic curve of genus g (Brill-Noether: d = ceil((2g + 6)/3)) with
#  (d-1)(d-2)/2 - g nodes at random points, its adjoints A (degree d - 3,
#  through the nodes: the canonical differentials A dx/F_y) and the exact
#  quadrics through the canonical model ((g-2)(g-3)/2 of them).
#
#    g   d   nodes   quadrics   odd characteristics   even characteristics
#    5   6     5        3              496                   528
#    6   6     4        6             2016                  2080
#    7   7     8       10             8128                  8256
#    8   8    13       15            32640                 32896
#    9   8    12       21           130816                131328
#   10   9    18       28           523776                524800
#
#  compare_reconstructed_quadrics(curve, prec): the quadrics of
#  reconstruct_quadrics_data moved to the coordinates of the differentials
#  (numerical reduced echelon form, no recognition) against the exact ones.
#  test_random_quadrics(g; count, prec, kw...): a @testset over random curves.
#
################################################################################

using Test

# k distinct points of the integer grid range x range, no three collinear
function _random_points_general_position(k::Int, range)
  while true
    points = unique([(rand(range), rand(range)) for _ in 1:k])
    length(points) == k || continue
    collinear(p, q, r) = (q[1] - p[1]) * (r[2] - p[2]) == (q[2] - p[2]) * (r[1] - p[1])
    any(collinear(points[i], points[j], points[l]) for i in 1:k for j in i+1:k for l in j+1:k) && continue
    return points
  end
end

# An LLL reduced integer basis (rows) of the kernel of the rational matrix C
function _small_kernel_basis(C::QQMatrix)
  N = kernel(C; side = :right)
  ncols(N) == 0 && return zero_matrix(ZZ, 0, nrows(N))
  rows = [begin
            d = reduce(lcm, [denominator(N[i, j]) for i in 1:nrows(N)])
            [numerator(N[i, j] * d) for i in 1:nrows(N)]
          end for j in 1:ncols(N)]
  return lll(matrix(ZZ, length(rows), nrows(N), reduce(vcat, rows)))
end

@doc raw"""
    canonical_test_curve(g; coefficients = -3:3, node_range = -2:2) -> NamedTuple

A random generic curve of genus g >= 5 over QQ with known canonical model: a
plane curve F of the minimal degree d = ceil((2g + 6)/3) with
(d-1)(d-2)/2 - g ordinary nodes at random integer points in general
position (F a random combination with coefficients in `coefficients` of an
LLL reduced basis of the curves of degree d singular there). The adjoints
A_1..A_g (degree d - 3, through the nodes, LLL reduced) give the canonical
differentials A_i dx / F_y; `quadrics` are the (g-2)(g-3)/2 quadrics
sum c_ij X_i X_j with sum c_ij A_i A_j in (F). Returns `quadrics`, `plane`,
`numerators`, `nodes`. (The genus is checked by the Riemann surface, e.g.
in compare_reconstructed_quadrics.)
"""
function canonical_test_curve(g::Int; coefficients = -3:3, node_range = -2:2, max_tries::Int = 50)
  @req g >= 5 "Only for g >= 5."
  d = cld(2*g + 6, 3)
  delta = div((d - 1) * (d - 2), 2) - g
  R, (x, y) = polynomial_ring(QQ, [:x, :y]; cached = false)
  monomials(k) = [x^i * y^j for i in 0:k for j in 0:k - i]
  md, ma = monomials(d), monomials(d - 3)
  at(p, q) = evaluate(p, [QQ(q[1]), QQ(q[2])])
  for _ in 1:max_tries
    nodes = _random_points_general_position(delta, node_range)
    # degree d, singular at the nodes
    C = matrix(QQ, 3 * delta, length(md),
               [at(D(m), q) for q in nodes for D in (identity, p -> derivative(p, 1), p -> derivative(p, 2)) for m in md])
    B = _small_kernel_basis(C)
    nrows(B) > 0 || continue
    F = sum(rand(coefficients) * sum(B[k, j] * md[j] for j in eachindex(md)) for k in 1:nrows(B))
    total_degree(F) == d || continue
    fac = factor(F)
    length(fac) == 1 && all(e == 1 for (_, e) in fac) || continue
    # ordinary nodes: nonzero Hessian determinant
    Fxx, Fxy, Fyy = derivative(derivative(F, 1), 1), derivative(derivative(F, 1), 2), derivative(derivative(F, 2), 2)
    all(q -> !iszero(at(Fxx, q) * at(Fyy, q) - at(Fxy, q)^2), nodes) || continue
    # the adjoints
    Ba = _small_kernel_basis(matrix(QQ, delta, length(ma), [at(m, q) for q in nodes for m in ma]))
    nrows(Ba) == g || continue
    numerators = [sum(Ba[k, j] * ma[j] for j in eachindex(ma)) for k in 1:g]
    quadrics = _quadrics_through_numerators(numerators, F)
    length(quadrics) == div((g - 2) * (g - 3), 2) || continue
    return (quadrics = quadrics, plane = F, numerators = numerators, nodes = nodes)
  end
  error("No curve found in $max_tries tries.")
end

@doc raw"""
    riemann_surface_with_differentials(F, numerators, prec) -> RiemannSurface

The Riemann surface of the plane curve F (model = :original) with the
differentials A dx / F_y (A in `numerators`, the adjoints of F) as its basis,
instead of the basis of the function field: its big period matrix then
integrates exactly these (canonical) differentials, and the expensive
function field basis (maximal orders, factorization of its numerators) is
skipped. The genus is certified modulo a prime (_genus_mod_p: g_p <= g, and
g <= length(numerators) for adjoints of a curve with the nodes of
canonical_test_curve). Not for integration_method = :rigorous (whose bounds
use the function field basis).
"""
function riemann_surface_with_differentials(F::MPolyRingElem, numerators, prec::Int)
  g = length(numerators)
  p = next_prime(2^20)
  gp = nothing
  for _ in 1:20
    p = next_prime(p + 1)
    gp = try RSR._genus_mod_p(F, p) catch; nothing end
    gp === nothing || break
  end
  @req gp == g "The genus of F modulo $p is $gp, not $g."
  RS = RSR.riemann_surface(F, prec; superelliptic = false, model = :original)
  C = RSR.computational_model(RS)
  f = C.defining_polynomial
  R = parent(f)
  K = base_ring(R)
  to_R(q) = map_coefficients(c -> K(c), q; parent = R)
  Fc = to_R(F)
  @req iszero(leading_coefficient(f) * Fc - leading_coefficient(Fc) * f) "The computational model is not F."
  factor_set = [[to_R(A) for A in numerators]; derivative(Fc, 2)]
  factor_matrix = zeros(Int, g + 1, g)
  for k in 1:g
    factor_matrix[k, k] = 1
    factor_matrix[g + 1, k] = -1
  end
  min_pows = [minimum(factor_matrix[l, :]) for l in 1:g + 1]
  range_pows = [maximum(factor_matrix[l, :]) for l in 1:g + 1] - min_pows
  C.genus = g
  C.baker_basis = false
  hasfield(typeof(C), :inner_faces) && (C.inner_faces = RSR._newton_polygon_interior_points(f))
  C.differential_form_data = (factor_set, factor_matrix, min_pows, range_pows)
  return RS
end

@doc raw"""
    compare_reconstructed_quadrics(curve, prec; kw...) -> NamedTuple

For a curve of canonical_test_curve (or _g5, _g6): the big period matrix of
its canonical differentials at `prec` bits, the reconstructed quadrics moved
to these coordinates in numerical reduced echelon form
(reconstruct_rational_quadrics with numerical = true: no recognition), and
log2 of their largest difference from the exact echelon form with the same
pivots, relative to its largest coefficient (about -prec + the loss if the
reconstruction is right; about 0 if not). Also the times of the period
matrix and of the reconstruction. Keywords are passed to
reconstruct_quadrics_data (theta_method, sign_data, curve_sign_data,
fay_relations, ...).
"""
function compare_reconstructed_quadrics(curve, prec::Int; kw...)
  g = length(curve.numerators)
  t_periods = @elapsed begin
    RS = riemann_surface_with_differentials(curve.plane, curve.numerators, prec)
    Pi = RSR.big_period_matrix(RS)
  end
  t_reconstruction = @elapsed numerical = reconstruct_rational_quadrics(Pi; numerical = true, kw...)
  e2 = numerical.monomials
  A = matrix(QQ, length(curve.quadrics), length(e2), [QQ(coeff(q, e)) for q in curve.quadrics for e in e2])
  @req nrows(numerical.rref) == nrows(A) "$(nrows(numerical.rref)) quadrics reconstructed, $(nrows(A)) expected."
  Ex = inv(A[:, numerical.pivots]) * A
  CC = base_ring(numerical.rref)
  difference = maximum(RSR._abs64(numerical.rref[r, c] - CC(Ex[r, c])) for r in 1:nrows(Ex), c in 1:ncols(Ex))
  largest = maximum(abs(Float64(c)) for c in Ex)
  return (log2_difference = RSR._safe_log2(difference / largest), precision = prec,
          time_periods = t_periods, time_reconstruction = t_reconstruction,
          times = numerical.info.times, residuals = numerical.info)
end

@doc raw"""
    test_random_quadrics(g; count = 5, prec = 500, loss = div(prec, 4), coefficients = -3:3, kw...)
        -> Vector

A @testset: for `count` random curves of genus g (canonical_test_curve_g5,
_g6, canonical_test_curve for g >= 7) whether the reconstructed quadrics
agree with the exact ones to at least prec - loss bits
(compare_reconstructed_quadrics; errors count as failures). Returns the
results (or the errors, with the curve). Keywords are passed to
reconstruct_quadrics_data.
"""
function test_random_quadrics(g::Int; count::Int = 5, prec::Int = 500, loss::Int = div(prec, 4),
                              coefficients = -3:3, kw...)
  results = Any[]
  @testset "reconstructed quadrics, genus $g" begin
    for i in 1:count
      curve = g == 5 ? canonical_test_curve_g5(; coefficients = coefficients) :
              g == 6 ? canonical_test_curve_g6(; coefficients = coefficients) :
                       canonical_test_curve(g; coefficients = coefficients)
      result = try
        compare_reconstructed_quadrics(curve, prec; kw...)
      catch err
        (error = err, curve = curve)
      end
      push!(results, result)
      if hasproperty(result, :log2_difference)
        println("curve $i: log2 difference $(result.log2_difference), periods $(round(result.time_periods, digits = 1)) s, reconstruction $(round(result.time_reconstruction, digits = 1)) s")
        println("  stages: ", join(["$k $(round(v, digits = 1)) s" for (k, v) in Base.pairs(result.times)], ", "))
      else
        println("curve $i: ", sprint(showerror, result.error))
      end
      @test hasproperty(result, :log2_difference) && result.log2_difference < -(prec - loss)
    end
  end
  return results
end

################################################################################
#
#  Data without curves: a random period matrix
#
#  Riemann's theta formula, and with it the relations of the sign correction,
#  holds for every tau in the Siegel upper half space, and the relations
#  between the gradients of the odd theta functions used here are (if they
#  come from Riemann's formula, as Frobenius' formula does) identities too. The
#  sign data and the Fay relations can then be computed from a random tau,
#  without the period matrix of a curve. check_gradient_relations verifies
#  the latter: the kernel of the Fay relations at a random tau against the
#  true gradients (theta jets).
#
################################################################################

@doc raw"""
    random_siegel_matrix(g, prec; scale = 1.0) -> AcbMatrix

A random Siegel reduced period matrix tau = X + i Y of genus g at `prec`
bits: X with entries in [-1/2, 1/2], Y = A A^T + g I / 2 (A with entries in
[-1, 1]) times `scale`, then Hecke.siegel_reduction. Exact rational entries,
no radius. For sign data and Fay relations (find_sign_data,
find_fay_relations), which do not need a curve.
"""
function random_siegel_matrix(g::Int, prec::Int; scale::Float64 = 1.0)
  CC = AcbField(prec)
  r() = QQ(rand(-1000:1000), 1000)
  X = matrix(QQ, g, g, [r() / 2 for _ in 1:g^2])
  X = (X + transpose(X)) * QQ(1, 2)
  A = matrix(QQ, g, g, [r() for _ in 1:g^2])
  Y = A * transpose(A) + QQ(g, 2) * identity_matrix(QQ, g)
  s = QQ(round(Int, 1000 * scale), 1000)
  tau = matrix(CC, g, g, [CC(X[i, j], s * Y[i, j]) for i in 1:g for j in 1:g])
  return Hecke.siegel_reduction(tau)[2]
end

@doc raw"""
    check_gradient_relations(g, tau; relations = nothing, kw...) -> NamedTuple

Whether the Fay relations hold at tau (not necessarily a Jacobian): the
kernel K of odd_theta_gradient_kernel (dimension g, its residual) and the
residual of the true gradients of g + 3 odd theta functions (theta jets)
against K B (_gradient_coordinates; about -precision if they are in the
kernel). With the theta constants of theta_constants_duplication (heuristic
signs).
"""
function check_gradient_relations(g::Int, tau::AcbMatrix; relations = nothing, kw...)
  thetas, info = RSR.theta_constants_duplication(tau)
  @req info.reliable "The duplication is not reliable for this tau."
  K, q_K = odd_theta_gradient_kernel(g, thetas; relations = relations, kw...)
  _, q_B = _gradient_coordinates(tau, K)
  return (kernel_residual = q_K, gradient_residual = q_B)
end

@doc raw"""
    fay_singular_values(g, thetas, relations; count = 100) -> Vector{Float64}

The `count` smallest singular values of the Float64 matrix of the stored Fay
relations (row and column scaled by powers of 2 as in the kernel), in
increasing order, relative to the largest. With rank n - g there are g
values at rounding level (~1e-16) and then a gap. A diagnostic: an SVD of
an 8135 x 8128 complex matrix takes a few minutes.
"""
function fay_singular_values(g::Int, thetas, relations; count::Int = 100)
  LA = RSR.LinearAlgebra
  odd_indices = char_to_index.(collect.(odd_theta_characteristics(g)))
  n = length(odd_indices)
  setup = _fay_setup(g)
  structure = [_fay_relation_structure(g, w, sigma, setup) for (w, sigma) in relations]
  rows = _sparse_fay_rows(structure, thetas, odd_indices)
  A = zeros(ComplexF64, length(rows), n)
  for (i, (cols, vals)) in enumerate(rows), (j, v) in zip(cols, vals)
    A[i, j] = RSR._c64(v)
  end
  for _ in 1:2
    for i in axes(A, 1)
      e = maximum(abs, view(A, i, :)); e > 0 && (A[i, :] ./= exp2(round(log2(e))))
    end
    for j in axes(A, 2)
      e = maximum(abs, view(A, :, j)); e > 0 && (A[:, j] ./= exp2(round(log2(e))))
    end
  end
  s = LA.svdvals(A)
  return reverse(s[end - min(count, length(s)) + 1:end]) ./ s[1]
end
