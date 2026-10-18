# The cubic from its polar quadrics (exactly and numerically) and the
# determinant by Laplace expansion; with the long tests a plane quintic
# (Masiewicki's quintic, the cubic threefold of the other Prym).
@testset "Plane quintics and cubic threefolds" begin
  R, X = polynomial_ring(QQ, [:x1, :x2, :x3, :x4, :x5])
  F = X[1]^3 + 2*X[2]^3 - X[3]^3 + X[4]^3 + 3*X[5]^3 + X[1]*X[2]*X[3] - X[3]*X[4]*X[5] + 2*X[1]*X[5]^2
  partials = [derivative(F, i) for i in 1:5]
  mixed = [partials[1] + partials[2], partials[2] - 3*partials[3], partials[3], partials[4] + partials[1], partials[5]]
  G = RSM._cubic_from_polar_quadrics(mixed)
  @test G * leading_coefficient(F) == F * leading_coefficient(G)
  CC = AcbField(128)
  S, Y = polynomial_ring(CC, 5)
  numeric = [map_coefficients(CC, q; parent = S) for q in mixed]
  Gc = RSM._cubic_from_polar_quadrics(numeric)
  lead(p) = coeff(p, [3, 0, 0, 0, 0])
  @test all(RSM._abs64(coeff(Gc, e) / lead(Gc) - CC(coeff(F, e) // lead(F))) < 1e-20
            for e in RSM._exponent_vectors(5, 3))

  M = [X[1] X[2] R(1); X[3] R(2) X[4]; R(1) X[5] X[1]]
  @test RSM._laplace_determinant(M) == det(matrix(R, M))

  if riesrf_long_tests()
    F5 = plane_quintic_test_curve()
    RS = RSM.riemann_surface(F5, 500; superelliptic = false, model = :original)
    tau = RSM.small_period_matrix(RS)
    data = RSM.reconstruct_curve_data(tau)
    @test data.case === :plane_quintic
    @test total_degree(data.curve) == 5
    @test total_degree(RSM.reconstruct_cubic_threefold(tau)) == 3
  end
end
