################################################################################
#
#  RieSrfDiagnostics/Reconstruction.jl : the reconstruction (genus g >= 5) on
#  random curves. Not part of the test run; load after the package:
#
#    using Hecke, Test
#    include("test/RieSrf/Reconstruction/setup_tests.jl")
#    include("test/RieSrfDiagnostics/Reconstruction.jl")
#    test_random_quadrics(5; count = 3)
#    test_random_plane_quintics(; count = 3)
#    test_random_hyperelliptic(5; count = 3)
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
#
#  random_siegel_matrix(g, prec): sign data and Fay relations of a new genus
#  do not need a curve (Riemann's and Fay's relations hold for every tau).
#
################################################################################

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

# The quadrics sum c_ij X_i X_j with sum c_ij A_i A_j = h F (A_i the adjoints
# of degree d - 3 of the plane curve F of degree d, h of degree d - 6)
function _quadrics_through_numerators(numerators, F)
  g = length(numerators)
  e2 = RSM._exponent_vectors(g, 2)
  x, y = gens(parent(F))
  k = 2 * maximum(total_degree, numerators) - total_degree(F)
  multiples = [F * x^i * y^j for i in 0:k for j in 0:k - i]
  polynomials = [[prod(numerators[i]^e[i] for i in 1:g) for e in e2]; multiples]
  monos = unique(vcat([collect(Hecke.monomials(p)) for p in polynomials]...))
  M = matrix(QQ, length(polynomials), length(monos), [coeff(p, m) for p in polynomials for m in monos])
  N = kernel(M; side = :left)
  S, X = polynomial_ring(QQ, ["X$i" for i in 1:g]; cached = false)
  return [sum(N[r, j] * prod(X[i]^e2[j][i] for i in 1:g) for j in eachindex(e2)) for r in 1:nrows(N)]
end

@doc raw"""
    canonical_test_curve(g; coefficients = -3:3, node_range = -2:2) -> NamedTuple

A random generic curve of genus g >= 5 over QQ with known canonical model:
`quadrics`, `plane` (F), `numerators` (the adjoints A: the differentials
A dx / F_y), `nodes`.
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
differentials A dx / F_y (A in `numerators`, the adjoints of F) as its basis:
its big period matrix integrates exactly these differentials (the expensive
function field basis is skipped). The genus is certified modulo a prime.
"""
function riemann_surface_with_differentials(F::MPolyRingElem, numerators, prec::Int)
  g = length(numerators)
  p = next_prime(2^20)
  gp = nothing
  for _ in 1:20
    p = next_prime(p + 1)
    gp = try RSM._genus_mod_p(F, p) catch; nothing end
    gp === nothing || break
  end
  @req gp == g "The genus of F modulo $p is $gp, not $g."
  RS = RSM.riemann_surface(F, prec; superelliptic = false, model = :original)
  C = RSM.computational_model(RS)
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
  hasfield(typeof(C), :inner_faces) && (C.inner_faces = RSM._newton_polygon_interior_points(f))
  C.differential_form_data = (factor_set, factor_matrix, min_pows, range_pows)
  return RS
end

@doc raw"""
    compare_reconstructed_quadrics(curve, prec; kw...) -> NamedTuple

For a curve of canonical_test_curve: the reconstructed quadrics in the
coordinates of its canonical differentials (numerical echelon form) against
the exact ones: log2 of the largest difference relative to the largest
coefficient (about -prec plus the loss if the reconstruction is right).
"""
function compare_reconstructed_quadrics(curve, prec::Int; kw...)
  t_periods = @elapsed begin
    RS = riemann_surface_with_differentials(curve.plane, curve.numerators, prec)
    P = RSM.big_period_matrix(RS)
  end
  t_reconstruction = @elapsed numerical = RSM.reconstruct_quadrics(P, nothing; numerical = true, kw...)
  e2 = numerical.monomials
  A = matrix(QQ, length(curve.quadrics), length(e2), [QQ(coeff(q, e)) for q in curve.quadrics for e in e2])
  @req nrows(numerical.rref) == nrows(A) "$(nrows(numerical.rref)) quadrics reconstructed, $(nrows(A)) expected."
  Ex = inv(A[:, numerical.pivots]) * A
  CC = base_ring(numerical.rref)
  difference = maximum(RSM._abs64(numerical.rref[r, c] - CC(Ex[r, c])) for r in 1:nrows(Ex), c in 1:ncols(Ex))
  largest = maximum(abs(Float64(c)) for c in Ex)
  return (log2_difference = RSM._safe_log2(difference / largest), precision = prec,
          time_periods = t_periods, time_reconstruction = t_reconstruction, info = numerical.info)
end

@doc raw"""
    test_random_quadrics(g; count = 5, prec = 500, loss = div(prec, 4), kw...) -> Vector

A @testset: for `count` random curves of genus g (canonical_test_curve)
whether the reconstructed quadrics agree with the exact ones to at least
prec - loss bits. Keywords are passed to reconstruct_quadrics.
"""
function test_random_quadrics(g::Int; count::Int = 5, prec::Int = 500, loss::Int = div(prec, 4),
                              coefficients = -3:3, kw...)
  results = Any[]
  @testset "reconstructed quadrics, genus $g" begin
    for i in 1:count
      curve = canonical_test_curve(g; coefficients = coefficients)
      result = try
        compare_reconstructed_quadrics(curve, prec; kw...)
      catch err
        (error = err, curve = curve)
      end
      push!(results, result)
      if hasproperty(result, :log2_difference)
        println("curve $i: log2 difference $(result.log2_difference), periods $(round(result.time_periods, digits = 1)) s, reconstruction $(round(result.time_reconstruction, digits = 1)) s")
      else
        println("curve $i: ", sprint(showerror, result.error))
      end
      @test hasproperty(result, :log2_difference) && result.log2_difference < -(prec - loss)
    end
  end
  return results
end

@doc raw"""
    random_siegel_matrix(g, prec; scale = 1.0) -> AcbMatrix

A random Siegel reduced period matrix of genus g at `prec` bits (for
find_sign_data and find_fay_relations, which do not need a curve).
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
    test_random_plane_quintics(; count = 3, prec = 500, kw...) -> Vector

For `count` random smooth plane quintics: the type found by
reconstruct_curve_data (:plane_quintic), Masiewicki's quintic, the canonical
model over QQ (checked exactly on the differentials) and the cubic threefold
of the Prym with kappa + eta odd (reconstruct_cubic_threefold).
"""
function test_random_plane_quintics(; count::Int = 3, prec::Int = 500, kw...)
  results = Any[]
  @testset "plane quintics" begin
    for i in 1:count
      F = plane_quintic_test_curve()
      result = try
        RS = RSM.riemann_surface(F, prec; superelliptic = false, model = :original)
        tau = RSM.small_period_matrix(RS)
        t = @elapsed data = RSM.reconstruct_curve_data(tau; kw...)
        model = RSM.reconstruct_curve(RSM.big_period_matrix(RS), QQ; kw...)
        to_F, ys = _differentials_in_function_field(RS)
        exact = all(q -> iszero(evaluate(map_coefficients(QQ, q), ys)), model)
        cubic = RSM.reconstruct_cubic_threefold(tau)
        (case = data.case, quintic = data.curve, model = model, exact = exact, cubic = cubic, time = t)
      catch err
        (error = err, curve = F)
      end
      push!(results, result)
      if hasproperty(result, :case)
        println("quintic $i: $(result.case), canonical model over QQ exact: $(result.exact), ",
                "cubic threefold of degree $(total_degree(result.cubic)) ($(round(result.time, digits = 1)) s)")
      else
        println("quintic $i: ", sprint(showerror, result.error))
      end
      @test hasproperty(result, :case) && result.case === :plane_quintic && result.exact
    end
  end
  return results
end

@doc raw"""
    test_random_hyperelliptic(g; count = 3, prec = 300) -> Vector

For `count` random hyperelliptic curves y^2 = h(x) of genus g (h monic of
degree 2g + 1): the Rosenhain form over CC against the branch points
(moebius_distance) and the curve over QQ from the big period matrix.
"""
function test_random_hyperelliptic(g::Int; count::Int = 3, prec::Int = 300, coefficients = -3:3)
  results = Any[]
  Qt, t = polynomial_ring(QQ, :t; cached = false)
  R, (x, y) = polynomial_ring(QQ, [:x, :y]; cached = false)
  @testset "hyperelliptic curves, genus $g" begin
    for i in 1:count
      h = t^(2*g + 1) + sum(QQ(rand(coefficients)) * t^k for k in 0:2*g)
      is_squarefree(h) || continue
      RS = RSM.riemann_surface(y^2 - h(x), prec)
      data = RSM.reconstruct_curve_data(RSM.small_period_matrix(RS))
      distance = moebius_distance(h, data.rosenhain)
      C = RSM.reconstruct_hyperelliptic_curve(RSM.big_period_matrix(RS), QQ)
      f = Hecke.hyperelliptic_polynomials(C)[1]
      same = f == map_coefficients(QQ, h; parent = parent(f))
      println("curve $i: $(data.case), Moebius distance 2^$(round(distance, digits = 1)), over QQ: $same")
      push!(results, (h = h, case = data.case, distance = distance, same = same))
      @test data.case === :hyperelliptic && distance < -prec / 2 && same
    end
  end
  return results
end
