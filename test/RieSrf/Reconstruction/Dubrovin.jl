# The quartics of the Dubrovin threefold: Trott's quartic exactly (in the
# coordinates of Baker's basis), a generic genus 4 curve (5 quartics in the
# ideal of the reconstructed quadric and cubic, vanishing on the curve) and
# the quartics over CC (the normalized coordinates do not depend on the
# Siegel reduction).
@testset "Dubrovin quartics" begin
  R, (x, y) = polynomial_ring(QQ, [:x, :y])
  trott = 144*x^4 + 144*y^4 - 225*x^2 - 225*y^2 + 350*x^2*y^2 + 81
  RS = RSM.riemann_surface(trott, 200; superelliptic = false, model = :original)
  Q = RSM.dubrovin_quartics(RSM.big_period_matrix(RS), QQ)
  @test length(Q) == 1
  ys = _differentials_in_function_field(RS)[2]
  @test iszero(evaluate(Q[1], ys))
  # Baker's basis is (1, x, y) dx / f_y: the quartic is trott(x2/x1, x3/x1) x1^4
  S = parent(Q[1])
  X = gens(S)
  F = sum(c * X[2]^e[1] * X[3]^e[2] * X[1]^(4 - e[1] - e[2]) for (c, e) in zip(coefficients(trott), Hecke.exponent_vectors(trott)))
  @test Q[1] * leading_coefficient(F) == F * leading_coefficient(Q[1])

  # over CC: one quartic, vanishing at the canonical image of the curve
  # (proportional to the one over QQ after the change of coordinates)
  tau = RSM.small_period_matrix(RS)
  Qc = RSM.dubrovin_quartics(tau)
  @test length(Qc) == 1

  Hecke.Random.seed!(4711)
  f = _random_g4_curve(:generic)
  RS = RSM.riemann_surface(f, 300; superelliptic = false, model = :original)
  P = RSM.big_period_matrix(RS)
  Q = RSM.dubrovin_quartics(P, QQ)
  @test length(Q) == 5
  ys = _differentials_in_function_field(RS)[2]
  @test all(q -> iszero(evaluate(q, ys)), Q)
  quadric, cubic = RSM.reconstruct_curve(P, QQ)
  S = parent(Q[1])
  X = gens(S)
  to_S(p) = map_coefficients(c -> QQ(c), p; parent = S)
  multiples = [[to_S(quadric) * X[i] * X[j] for i in 1:4 for j in i:4]; [to_S(cubic) * X[i] for i in 1:4]]
  e4 = RSM._exponent_vectors(4, 4)
  M(fs) = matrix(QQ, length(fs), length(e4), [coeff(p, e) for p in fs for e in e4])
  @test rank(vcat(M(multiples), M(Q))) == rank(M(multiples)) == 14
end
