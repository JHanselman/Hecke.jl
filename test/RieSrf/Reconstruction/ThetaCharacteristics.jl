# The characteristics, the Prym index pairs, and Igusa's transformation
# formula (_transform_theta_constants) against FLINT's theta constants at the
# transformed period matrix.
@testset "Theta characteristics" begin
  @test length(RSM.odd_theta_characteristics(3)) == 28
  @test length(RSM.even_theta_characteristics(3)) == 36
  pairs = RSM.lift_prym_indices(5)
  odds = RSM.odd_theta_characteristics(5)
  @test length(pairs) == length(RSM.odd_theta_characteristics(4))
  @test all(odds[i][1] == 0 && odds[j][1] == 0 && odds[i][6] == 0 && odds[j][6] == 1 for (i, j) in pairs)

  CC = AcbField(128)
  tau = matrix(CC, 2, 2, [CC(0.31, 1.13), CC(0.17, 0.41), CC(0.17, 0.41), CC(-0.22, 0.97)])
  thetas = RSM.theta_constants(tau)
  standard = [0, 0, 1, 0]
  for eta in ([1, 0, 0, 0], [0, 1, 1, 1], [1, 1, 0, 1])
    M = RSM._eta_to_standard(eta, 2)
    @test RSM._f2(RSM._char_linear_part(M, 2) * eta) == standard
    moved = RSM._transform_theta_constants(thetas, M, 2)
    direct = RSM.theta_constants(Hecke.siegel_transform(matrix(ZZ, M), tau))
    evens = [c for c in keys(direct) if RSM._is_even(c)]
    ratios = [direct[c] / moved[c] for c in evens]
    @test all(r -> RSM._abs64(r - ratios[1]) < 1e-20 * RSM._abs64(ratios[1]), ratios)
  end
end
