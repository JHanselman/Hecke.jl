# A hyperelliptic curve of genus 5: the type, the Rosenhain form against the
# branch points (Moebius map) and the curve over QQ from the big period matrix.
@testset "Reconstruction of hyperelliptic curves" begin
  Hecke.Random.seed!(4711)
  Qt, t = polynomial_ring(QQ, :t)
  R, (x, y) = polynomial_ring(QQ, [:x, :y])
  h = t^11 - 3*t^9 + 2*t^7 + t^6 - 5*t^4 + t^3 + 2*t - 1
  @test is_squarefree(h)
  prec = 300
  RS = RSM.riemann_surface(y^2 - h(x), prec)
  data = RSM.reconstruct_curve_data(RSM.small_period_matrix(RS))
  @test data.case === :hyperelliptic
  @test moebius_distance(h, data.rosenhain) < -prec / 2
  C = RSM.reconstruct_hyperelliptic_curve(RSM.big_period_matrix(RS), QQ)
  f = Hecke.hyperelliptic_polynomials(C)[1]
  @test f == map_coefficients(QQ, h; parent = parent(f))
end
