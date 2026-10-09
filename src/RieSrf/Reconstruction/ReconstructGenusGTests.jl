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
        println("  stages: ", join(["$k $(round(v, digits = 1)) s" for (k, v) in zip(keys(result.times), values(result.times))], ", "))
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

################################################################################
#
#  Off the Jacobian locus: the Pryms of random genus 6 curves
#
################################################################################

# The small period matrix of a big period matrix (symmetrized)
function _small_period_matrix(Pi::AcbMatrix)
  g = nrows(Pi)
  tau = RSR._solve_precond(Pi[:, 1:g], Pi[:, g+1:2*g])
  return (tau + transpose(tau)) * inv(base_ring(Pi)(2))
end

# A summary of the info of reconstruct_quadrics_from_thetas: the residuals,
# the number of quadrics found (singular values of the relation matrix above
# 2^(-prec/2); (g-2)(g-3)/2 for a generic Jacobian) and the singular values:
# with diagnostics, all of them at full precision (log2, relative) for the
# squares and for the relation matrix, and log2 of the smallest of the
# Float64 Fay matrices of the curve and of its Prym
function _quadrics_summary(info, g::Int, prec::Int)
  r1(x) = round(x, digits = 1)
  log2s(v) = [r1(RSR._safe_log2(x)) for x in v]
  if hasproperty(info, :quadric_singular_values_log2)
    quadric_sv = r1.(info.quadric_singular_values_log2)
    squares_sv = r1.(info.squares_singular_values_log2)
    rank = count(>(-prec / 2), info.quadric_singular_values_log2)
  else
    quadric_sv = log2s(info.quadric_singular_values)
    squares_sv = Float64[]
    rank = count(>(2.0^(-prec / 2)), info.quadric_singular_values)
  end
  fay_sv = hasproperty(info, :fay_singular_values) ? log2s(info.fay_singular_values) : Float64[]
  prym_fay_sv = hasproperty(info, :prym_fay_singular_values) ? log2s(info.prym_fay_singular_values) : Float64[]
  return (gradients = info.gradients, prym_gradients = info.prym_gradients,
          relations = info.relations, quadrics = info.quadrics,
          rank = rank, expected = div((g - 2) * (g - 3), 2),
          quadric_singular_values_log2 = quadric_sv, squares_singular_values_log2 = squares_sv,
          fay_singular_values_log2 = fay_sv, prym_fay_singular_values_log2 = prym_fay_sv)
end

function _show_quadrics_summary(label, summary)
  println(label, ":")
  println("  residuals (log2): gradients $(summary.gradients), prym gradients $(summary.prym_gradients), ",
          "relations $(summary.relations), quadrics $(summary.quadrics)")
  println("  quadrics found: $(summary.rank) (generic Jacobian: $(summary.expected))")
  println("  singular values (log2, relative), relation matrix: ", summary.quadric_singular_values_log2)
  isempty(summary.squares_singular_values_log2) ||
    println("  singular values (log2, relative), squares of the Prym gradients: ", summary.squares_singular_values_log2)
  isempty(summary.fay_singular_values_log2) ||
    println("  smallest singular values (log2, Float64), Fay matrix: ", summary.fay_singular_values_log2)
  isempty(summary.prym_fay_singular_values_log2) ||
    println("  smallest singular values (log2, Float64), Fay matrix of its Prym: ", summary.prym_fay_singular_values_log2)
end

@doc raw"""
    test_random_prym_quadrics(; count = 5, prec = 500, control = true, coefficients = -3:3,
                              curve_sign_data, prym_sign_data, sign_data, kw...) -> Vector

For `count` random genus 6 curves (canonical_test_curve_g6, period matrix of
riemann_surface_with_differentials at `prec` bits): prym_quadrics, i.e. the
reconstruction of quadrics applied to the theta constants of the Prym
(dimension 5, a generic principally polarized abelian variety, not a
Jacobian). Prints per curve the residuals (log2; about -prec if the
relations hold), the number of quadrics found (3 for a genus 5 Jacobian)
and the singular values (_show_quadrics_summary: all of them, at full
precision, for the relation matrix and the squares; the smallest of the
Float64 Fay matrices). With
`control`, the same for a random genus 5 curve (canonical_test_curve_g5,
reconstruct_quadrics_from_thetas), for comparison. `curve_sign_data`: genus
6 (for theta_method = :riemann), `prym_sign_data`: genus 5, `sign_data`:
genus 4; further keywords are passed to prym_quadrics. Returns the
summaries (or the errors, with the curves).
"""
function test_random_prym_quadrics(; count::Int = 5, prec::Int = 500, control::Bool = true,
                                   coefficients = -3:3, curve_sign_data = nothing,
                                   prym_sign_data = nothing, sign_data = nothing, kw...)
  results = Any[]
  show = _show_quadrics_summary
  if control
    curve = canonical_test_curve_g5(; coefficients = coefficients)
    try
      RS = riemann_surface_with_differentials(curve.plane, curve.numerators, prec)
      _, tau = Hecke.siegel_reduction(_small_period_matrix(RSR.big_period_matrix(RS)))
      thetas = _theta_constants_by_method(tau, :riemann; curve_sign_data = prym_sign_data)
      J = reconstruct_quadrics_from_thetas(5, thetas; sign_data = sign_data, strict = false, diagnostics = true)
      summary = _quadrics_summary(J.info, 5, prec)
      push!(results, (jacobian = true, summary = summary, curve = curve))
      show("genus 5 Jacobian (control)", summary)
    catch err
      push!(results, (jacobian = true, error = err, curve = curve))
      println("genus 5 Jacobian (control): ", sprint(showerror, err))
    end
  end
  for i in 1:count
    curve = canonical_test_curve_g6(; coefficients = coefficients)
    try
      t = @elapsed begin
        RS = riemann_surface_with_differentials(curve.plane, curve.numerators, prec)
        tau = _small_period_matrix(RSR.big_period_matrix(RS))
        P = prym_quadrics(tau; curve_sign_data = curve_sign_data, prym_sign_data = prym_sign_data,
                          sign_data = sign_data, kw...)
      end
      summary = _quadrics_summary(P.info, 5, prec)
      push!(results, (jacobian = false, summary = summary, curve = curve, quadrics = P.quadrics))
      show("Prym $i ($(round(t, digits = 1)) s)", summary)
    catch err
      push!(results, (jacobian = false, error = err, curve = curve))
      println("Prym $i: ", sprint(showerror, err))
    end
  end
  return results
end

################################################################################
#
#  Pryms of plane quintics
#
#  A smooth plane quintic C has genus 6 and the odd theta characteristic
#  kappa = O(1) with h^0 = 3: grad theta[kappa](0) = 0. By Mumford, the Prym
#  of C for eta is a Jacobian (of a genus 5 curve) if h^0(kappa + eta) is
#  even, and the intermediate Jacobian of a cubic threefold (not a Jacobian)
#  if it is odd. The parity of h^0(kappa + eta) is that of the
#  characteristic kappa + eta; for the eta = (0..0; 1 0..0) of prym_thetas
#  (b_1 = 1) it is even iff a_1(kappa) = 1.
#
################################################################################

@doc raw"""
    plane_quintic_test_curve(; coefficients = -3:3) -> MPolyRingElem

A random smooth plane quintic F(x, y) over QQ (coefficients in `coefficients`,
full Newton polygon; smooth, i.e. genus 6, certified modulo a prime as for
Baker's basis).
"""
function plane_quintic_test_curve(; coefficients = -3:3)
  R, (x, y) = polynomial_ring(QQ, [:x, :y]; cached = false)
  while true
    F = sum(QQ(rand(coefficients)) * x^i * y^j for i in 0:5 for j in 0:5 - i)
    total_degree(F) == 5 || continue
    length(RSR._newton_polygon_interior_points(F)) == 6 || continue
    RSR._baker_certified(F, 6) || continue
    return F
  end
end

@doc raw"""
    test_random_plane_quintic_pryms(; count = 5, prec = 500, coefficients = -3:3, curve_fay_relations = nothing,
                                    curve_sign_data, prym_sign_data, sign_data, kw...) -> Vector

For `count` random smooth plane quintics (plane_quintic_test_curve, genus 6,
Baker's basis, `prec` bits): prym_quadrics (the reconstruction applied to the
Prym for eta = (0..0; 1 0..0)), and the type of this Prym: kappa = O(1) is
the odd characteristic whose gradient vanishes (the zero row of the Fay
kernel of the quintic, with `curve_fay_relations`, the genus 6 relations;
`kappa_gap`: log2 of the ratio of its row to the next smallest), and the
Prym is a Jacobian iff kappa + eta is even (Mumford). Prints this and the
summary of _show_quadrics_summary per curve. `curve_sign_data`: genus 6,
`prym_sign_data`: genus 5, `sign_data`: genus 4; further keywords are passed
to prym_quadrics.
"""
function test_random_plane_quintic_pryms(; count::Int = 5, prec::Int = 500, coefficients = -3:3,
                                         curve_fay_relations = nothing, curve_sign_data = nothing,
                                         prym_sign_data = nothing, sign_data = nothing, kw...)
  results = Any[]
  odds = odd_theta_characteristics(6)
  for i in 1:count
    F = plane_quintic_test_curve(; coefficients = coefficients)
    try
      t = @elapsed begin
        RS = RSR.riemann_surface(F, prec; superelliptic = false, model = :original)
        tau = _small_period_matrix(RSR.big_period_matrix(RS))
        P = prym_quadrics(tau; curve_sign_data = curve_sign_data, prym_sign_data = prym_sign_data,
                          sign_data = sign_data, kw...)
        K, _ = odd_theta_gradient_kernel(6, P.curve_thetas; relations = curve_fay_relations)
      end
      norms = [maximum(RSR._abs64(K[r, c]) for c in 1:6) for r in 1:nrows(K)]
      order = sortperm(norms)
      kappa = odds[order[1]]
      kappa_gap = RSR._safe_log2(norms[order[1]] / norms[order[2]])
      jacobian = isodd(kappa[1])
      summary = _quadrics_summary(P.info, 5, prec)
      push!(results, (curve = F, kappa = kappa, kappa_gap = kappa_gap, prym_is_jacobian = jacobian,
                      summary = summary, quadrics = P.quadrics))
      println("plane quintic $i ($(round(t, digits = 1)) s): kappa = $kappa (gap 2^$(round(kappa_gap, digits = 1))), ",
              "kappa + eta ", jacobian ? "even: the Prym is a Jacobian" : "odd: the Prym is the intermediate Jacobian of a cubic threefold")
      _show_quadrics_summary("  Prym", summary)
    catch err
      push!(results, (curve = F, error = err))
      println("plane quintic $i: ", sprint(showerror, err))
    end
  end
  return results
end

################################################################################
#
#  Does the reconstruction separate Jacobians from non-Jacobians?
#
################################################################################

struct _ImpreciseTau <: Exception
  bits::Float64
end

# One line of evidence of classify_jacobian
function _evidence_line(c)
  e = c.evidence
  parts = String[]
  haskey(e, :schottky_jung_rank) && push!(parts, "Schottky-Jung rank $(e.schottky_jung_rank)/$(e.schottky_jung_needed)")
  haskey(e, :gradient_residual) && push!(parts, "Fay residual $(round(e.gradient_residual, digits = 1))")
  haskey(e, :prym_gradient_residual) && push!(parts, "Prym Fay residual $(e.prym_gradient_residual)")
  haskey(e, :squares_singular_values_log2) &&
    push!(parts, "smallest squares singular value 2^$(round(minimum(e.squares_singular_values_log2), digits = 1))")
  haskey(e, :quadric_count) && push!(parts, "quadrics $(e.quadric_count) (gap $(round(e.quadric_gap_bits, digits = 1)) bits)")
  haskey(e, :quadric_singular_values_log2) &&
    push!(parts, "relation matrix singular values (log2) $(round.(e.quadric_singular_values_log2[1:min(7, end)], digits = 1))")
  for key in (:schottky_jung_error, :gradient_kernel_error, :prym_gradient_kernel_error)
    haskey(e, key) && push!(parts, "$key: $(first(e[key], 120))")
  end
  return join(parts, "; ")
end

@doc raw"""
    hyperelliptic_test_curve(g; coefficients = -3:3) -> MPolyRingElem

y^2 - f(x) for a random squarefree f of degree 2g + 2 with coefficients in
`coefficients` (a hyperelliptic curve of genus g).
"""
function hyperelliptic_test_curve(g::Int; coefficients = -3:3)
  Qt, t = polynomial_ring(QQ, :t; cached = false)
  R, (x, y) = polynomial_ring(QQ, [:x, :y]; cached = false)
  while true
    f = sum(QQ(rand(coefficients)) * t^i for i in 0:2*g+2)
    degree(f) == 2*g + 2 && is_squarefree(f) || continue
    return y^2 - sum(coeff(f, i) * x^i for i in 0:2*g+2)
  end
end

@doc raw"""
    product_period_matrix(partition, prec; coefficients = -3:3) -> AcbMatrix, Vector

The block diagonal period matrix of a product of Jacobians of dimensions
`partition` (e.g. [2, 3]), Siegel reduced: random_siegel_matrix for
dimensions 1, 2, 3 (a generic principally polarized abelian variety of
dimension at most 3 is a Jacobian), a random plane curve of genus 4
(the genus 4 tests' _random_g4_curve(:generic)) for 4, a random canonical
curve of genus 5 for 5. Also returns the curves (nothing for the random
matrices).
"""
function product_period_matrix(partition::Vector{Int}, prec::Int; coefficients = -3:3)
  @req all(h -> 1 <= h <= 5, partition) "The dimensions must be between 1 and 5."
  CC = AcbField(prec)
  g = sum(partition)
  T = zero_matrix(CC, g, g)
  curves = Any[]
  offset = 0
  for h in partition
    if h <= 3
      tau = random_siegel_matrix(h, prec)
      push!(curves, nothing)
    elseif h == 4
      tau = nothing
      for _ in 1:20
        f = RSR._random_g4_curve(:generic; coeff_range = coefficients)
        RS = RSR.riemann_surface(f, prec; superelliptic = false, model = :original)
        t = _small_period_matrix(RSR.big_period_matrix(RS))
        nrows(t) == 4 || continue
        tau = t
        push!(curves, f)
        break
      end
      @req tau !== nothing "No curve of genus 4 found."
    else
      curve = canonical_test_curve_g5(; coefficients = coefficients)
      RS = riemann_surface_with_differentials(curve.plane, curve.numerators, prec)
      tau = _small_period_matrix(RSR.big_period_matrix(RS))
      push!(curves, curve.plane)
    end
    for i in 1:h, j in 1:h
      T[offset + i, offset + j] = CC(tau[i, j])
    end
    offset += h
  end
  return Hecke.siegel_reduction(T)[2], curves
end

@doc raw"""
    test_jacobian_classification(; jacobians = 3, generic_pryms = 3, quintics = 6, hyperelliptic = 2,
                                 products = 1, partitions = [[1, 4], [2, 3], [1, 1, 3], [1, 2, 2], [1, 1, 1, 2]],
                                 prec = 500,
                                 curve_sign_data_5, curve_sign_data_6, sign_data_4, fay_relations_6,
                                 certified_fixed_signs = false, gap_bits = nothing) -> Vector

A @testset for classify_jacobian on principally polarized abelian varieties
of dimension 5 whose type is known:

  - Jacobians of random genus 5 curves (canonical_test_curve_g5): :jacobian;
  - Pryms of random genus 6 curves (canonical_test_curve_g6; generic, not
    Jacobians): :not_jacobian;
  - Pryms of random smooth plane quintics (plane_quintic_test_curve): by
    Mumford a Jacobian if kappa + eta is even (kappa = O(1), the odd
    characteristic with vanishing gradient, found from the Fay kernel of the
    quintic), the intermediate Jacobian of a cubic threefold if it is odd:
    :jacobian resp. :not_jacobian;
  - Jacobians of random hyperelliptic curves of genus 5
    (hyperelliptic_test_curve) and `products` products of Jacobians for each
    partition of 5 in `partitions` (product_period_matrix): not tested
    (expected :unknown), only reported, to see what the reconstruction does.
    These have vanishing even theta constants, so their theta constants come
    from acb_theta_all and classify_jacobian runs with allow_vanishing.

The sign data: `curve_sign_data_5` (genus 5; the Jacobians and the signs of
the Pryms), `curve_sign_data_6` (genus 6, the theta constants of the genus
6 curves), `sign_data_4` (genus 4, for classify_jacobian); `fay_relations_6`
for the Fay kernel of the quintics. Prints per case the expected and the
found verdict with the evidence, and a summary. :inconclusive counts as a
failure, except for a period matrix known to less than half the precision
(reported as :inconclusive at stage :period_matrix and not tested: a
problem of the period matrix, not of the classification). Returns the
results.
"""
function test_jacobian_classification(; jacobians::Int = 3, generic_pryms::Int = 3, quintics::Int = 6,
                                      hyperelliptic::Int = 2, products::Int = 1,
                                      partitions = [[1, 4], [2, 3], [1, 1, 3], [1, 2, 2], [1, 1, 1, 2]],
                                      prec::Int = 500, coefficients = -3:3, curve_sign_data_5 = nothing,
                                      curve_sign_data_6 = nothing, sign_data_4 = nothing,
                                      fay_relations_6 = nothing, certified_fixed_signs::Bool = false,
                                      gap_bits = nothing)
  results = Any[]
  odds6 = odd_theta_characteristics(6)
  # the period matrix must be known to at least half the precision (some
  # curves give large radii): else :inconclusive, before the theta constants
  struct_precision(tau) = -maximum(RSR._log2_relative_radius(tau[i, j]) for i in 1:nrows(tau), j in 1:ncols(tau))
  function thetas_of(tau, data)
    bits = struct_precision(tau)
    bits < prec / 2 && throw(_ImpreciseTau(bits))
    return _theta_constants_by_method(Hecke.siegel_reduction(tau)[2], :riemann; curve_sign_data = data,
                                      certified_fixed_signs = certified_fixed_signs)
  end
  classify(thetas; allow_vanishing = false) = classify_jacobian(5, thetas; sign_data = sign_data_4, gap_bits = gap_bits,
                                                                allow_vanishing = allow_vanishing)
  # with vanishing even theta constants (hyperelliptic curves, products) the
  # signs by Riemann's relations are not available: acb_theta_all
  function thetas_flint(tau)
    bits = struct_precision(tau)
    bits < prec / 2 && throw(_ImpreciseTau(bits))
    t = Hecke.siegel_reduction(tau)[2]
    return Hecke.thetas([zero(base_ring(t)) for _ in 1:nrows(t)], t)
  end
  function record(kind, expected, compute)
    t = time()
    found = try
      compute()
    catch err
      err isa _ImpreciseTau ?
        (verdict = :inconclusive, stage = :period_matrix, error = "period matrix known to $(round(err.bits, digits = 1)) bits only", extra = "") :
        (verdict = :error, stage = :setup, error = sprint(showerror, err), extra = "")
    end
    line = hasproperty(found, :classification) ? _evidence_line(found.classification) : found.error
    extra = hasproperty(found, :extra) ? found.extra : ""
    println(rpad(kind, 34), " expected $(rpad(string(expected), 13)) found $(rpad(string(found.verdict), 13)) ",
            "($(found.stage), $(round(time() - t, digits = 1)) s) $extra")
    println("    ", line)
    push!(results, (kind = kind, expected = expected, verdict = found.verdict, stage = found.stage, result = found))
  end
  for i in 1:jacobians
    record("genus 5 Jacobian $i", :jacobian, () -> begin
      curve = canonical_test_curve_g5(; coefficients = coefficients)
      RS = riemann_surface_with_differentials(curve.plane, curve.numerators, prec)
      c = classify(thetas_of(_small_period_matrix(RSR.big_period_matrix(RS)), curve_sign_data_5))
      (verdict = c.verdict, stage = c.stage, classification = c, curve = curve)
    end)
  end
  for i in 1:generic_pryms
    record("Prym of a genus 6 curve $i", :not_jacobian, () -> begin
      curve = canonical_test_curve_g6(; coefficients = coefficients)
      RS = riemann_surface_with_differentials(curve.plane, curve.numerators, prec)
      thetas = thetas_of(_small_period_matrix(RSR.big_period_matrix(RS)), curve_sign_data_6)
      thetas_P, _ = _prym_theta_constants(6, thetas, curve_sign_data_5)
      c = classify(thetas_P)
      (verdict = c.verdict, stage = c.stage, classification = c, curve = curve)
    end)
  end
  for i in 1:quintics
    F = plane_quintic_test_curve(; coefficients = coefficients)
    RS = RSR.riemann_surface(F, prec; superelliptic = false, model = :original)
    local thetas, kappa, gap, expected
    try
      thetas = thetas_of(_small_period_matrix(RSR.big_period_matrix(RS)), curve_sign_data_6)
      K, _ = odd_theta_gradient_kernel(6, thetas; relations = fay_relations_6)
      norms = [maximum(RSR._abs64(K[r, c]) for c in 1:6) for r in 1:nrows(K)]
      order = sortperm(norms)
      kappa, gap = odds6[order[1]], RSR._safe_log2(norms[order[1]] / norms[order[2]])
      expected = isodd(kappa[1]) ? :jacobian : :not_jacobian
    catch err
      message = err isa _ImpreciseTau ? "period matrix known to $(round(err.bits, digits = 1)) bits only" :
                sprint(showerror, err)
      verdict = err isa _ImpreciseTau ? :inconclusive : :error
      println(rpad("Prym of a plane quintic $i", 34), " type unknown, $verdict: ", message)
      push!(results, (kind = "Prym of a plane quintic $i", expected = :unknown, verdict = verdict,
                      stage = :setup, result = (curve = F, error = err)))
      continue
    end
    record("Prym of a plane quintic $i", expected, () -> begin
      thetas_P, _ = _prym_theta_constants(6, thetas, curve_sign_data_5)
      c = classify(thetas_P)
      (verdict = c.verdict, stage = c.stage, classification = c, curve = F, kappa = kappa,
       extra = "kappa $(kappa) (gap 2^$(round(gap, digits = 1)))")
    end)
  end
  # hyperelliptic curves and products of Jacobians (vanishing theta
  # constants; what the reconstruction does is the question: expected
  # :unknown)
  for i in 1:hyperelliptic
    record("hyperelliptic curve of genus 5 $i", :unknown, () -> begin
      F = hyperelliptic_test_curve(5; coefficients = coefficients)
      RS = RSR.riemann_surface(F, prec)
      c = classify(thetas_flint(_small_period_matrix(RSR.big_period_matrix(RS))); allow_vanishing = true)
      (verdict = c.verdict, stage = c.stage, classification = c, curve = F,
       extra = "$(c.evidence.vanishing_theta_constants) vanishing theta constants")
    end)
  end
  for partition in partitions, i in 1:products
    record("product $(join(partition, "+")) $i", :unknown, () -> begin
      tau, curves = product_period_matrix(partition, prec; coefficients = coefficients)
      c = classify(thetas_flint(tau); allow_vanishing = true)
      (verdict = c.verdict, stage = c.stage, classification = c, curves = curves,
       extra = "$(c.evidence.vanishing_theta_constants) vanishing theta constants")
    end)
  end
  println()
  for kind in ("genus 5 Jacobian", "Prym of a genus 6 curve", "Prym of a plane quintic",
               "hyperelliptic curve", "product")
    rs = filter(r -> startswith(r.kind, kind), results)
    isempty(rs) && continue
    found = join(["$v $(count(r -> r.verdict === v, rs))" for v in unique(r.verdict for r in rs)], ", ")
    if all(r -> r.expected === :unknown, rs)
      println(rpad(kind, 26), "found: ", found)
    else
      right = count(r -> r.verdict === r.expected, rs)
      println(rpad(kind, 26), "$right of $(length(rs)) as expected; found: ", found)
    end
  end
  @testset "Jacobians and non-Jacobians of dimension 5" begin
    for r in results
      (r.expected === :unknown || r.stage in (:period_matrix, :setup) && r.verdict === :inconclusive) && continue
      @test r.verdict === r.expected
    end
  end
  return results
end
