# theta_constants_duplication against Hecke.thetas (FLINT) for random reduced
# period matrices of genus 1-4.
@testset "ThetaDuplication" begin
  Hecke.Random.seed!(17)
  prec = 200
  CC = AcbField(prec)
  for g in 1:4
    entries = [CC(rand() - 0.5) for _ in 1:g, _ in 1:g]
    A = matrix(CC, g, g, [rand() - 0.5 for _ in 1:g*g])
    Y = A * transpose(A) + identity_matrix(CC, g)
    X = matrix(CC, g, g, [(entries[i, j] + entries[j, i]) / 2 for i in 1:g for j in 1:g])
    tau = X + onei(CC) * Y
    _, tau = Hecke.siegel_reduction(tau)
    reference = Hecke.thetas([zero(CC) for _ in 1:g], tau)
    for squared in (false, true)
      th, info = RSM.theta_constants_duplication(tau; squared = squared)
      @test info.sign_margin_intermediate < 0.1 && info.sign_margin_final < 0.1
      scale = maximum(abs(RSM._c64(x)) for x in values(reference))
      worst = maximum(abs(RSM._c64(th[k] - (squared ? reference[k]^2 : reference[k]))) for k in keys(reference))
      @test worst < 2.0^(-prec + 30) * scale^(squared ? 2 : 1)
    end
  end
end
