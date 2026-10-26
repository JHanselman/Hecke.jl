# Thomae's formula over any field: the fourth powers against the FLINT theta
# constants (moved to Mumford's basis as in _rosenhain_invariants), the squares
# over finite fields against Takase's formula and the quadratic relations.

# The theta constants of y^2 = h(x) in Mumford's standard basis and the
# Rosenhain invariants (the steps of _rosenhain_invariants)
function thomae_test_moved_thetas(h, prec)
  R, (x, y) = polynomial_ring(QQ, [:x, :y])
  RS = RSM.riemann_surface(y^2 - h(x), prec)
  tau = RSM.small_period_matrix(RS)
  g = nrows(tau)
  thetas, _, _ = RSM._reduced_theta_constants(tau)
  vanishing = RSM._vanishing_even_theta_constants(thetas, prec)
  eta, U = RSM._hyperelliptic_eta(g, thetas, vanishing)
  standard, U_standard = RSM._mumford_eta_standard(g)
  in_U = sort(setdiff(U, [2*g + 2]))
  order = zeros(Int, 2*g + 1)
  order[2:2:2*g] = in_U
  order[1:2:2*g + 1] = setdiff(1:2*g + 1, in_U)
  N = RSM._symplectic_lift([eta[order[k]] for k in 1:2*g], standard[1:2*g], g)
  J = [zeros(Int, g, g) Matrix{Int}(Hecke.LinearAlgebra.I, g, g); -Matrix{Int}(Hecke.LinearAlgebra.I, g, g) zeros(Int, g, g)]
  M = Matrix(transpose(-J * transpose(N) * J))
  moved = RSM._transform_theta_constants(thetas, M, g)
  lambdas = RSM._rosenhain_invariants(g, thetas, vanishing)
  return g, moved, lambdas
end

@testset "Thomae's formula" begin
  @testset "Fourth powers against FLINT" begin
    Qt, t = polynomial_ring(QQ, :t)
    prec = 200
    for h in [t^7 - 3*t^5 + 2*t^4 + t^3 - 5*t^2 + t + 2,
              t^8 + 2*t^7 - t^5 + 3*t^4 - t^3 + 2*t - 5]
      g, moved, lambdas = thomae_test_moved_thetas(h, prec)
      CC = parent(lambdas[1])
      fourth = RSM.thomae_theta_constants([zero(CC); one(CC); lambdas])
      reference = (0, 0, ntuple(_ -> 0, 2*g - 2)...)
      scale = moved[reference]^4 / fourth[reference]
      @test all(RSM._log2abs(moved[c]^4 - scale * fourth[c]) < -prec / 2 for c in keys(moved))
    end
  end

  @testset "Squares over finite fields" begin
    rng = Hecke.Random.MersenneTwister(17)
    for (K, genera) in [(GF(1009), 2:6), (finite_field(3, 5, "w")[1], 2:4)]
      for g in genera
        a = unique([rand(rng, K) for _ in 1:4*g + 8])[1:2*g + 1]
        squares = RSM.thomae_theta_constants(a; squares = true)
        fourth = RSM.thomae_theta_constants(a)
        L = parent(first(values(squares)))
        embedding = L === K ? identity : embed(K, L)
        @test all(squares[c]^2 == embedding(fourth[c]) for c in keys(fourth))
        @test RSM.theta_squares_relations_hold(squares)
        @test RSM.rosenhain_invariants_from_theta_squares(squares) ==
              [embedding(divexact(a[l] - a[1], a[2] - a[1])) for l in 3:2*g + 1]
        # a wrong sign breaks the relations
        c = first(k for k in keys(squares) if !iszero(squares[k]))
        broken = copy(squares)
        broken[c] = -broken[c]
        @test !RSM.theta_squares_relations_hold(broken)
      end
    end
  end

  @testset "Polynomials and 2g + 2 branch points" begin
    K = GF(101)
    Kx, x = polynomial_ring(K, :x)
    # irreducible factors of degree 2 and 3: the roots in GF(101^6)
    f = (x^2 + 2) * (x^3 + x + 1) * (x^2 + x + 3)
    @test is_squarefree(f)
    squares, a = RSM.thomae_theta_constants(f; squares = true)
    @test length(a) == 7 && all(iszero(f(y)) for y in a)
    @test RSM.theta_squares_relations_hold(squares)
    # 2g + 2 finite branch points: the same theta^4 as with the last one moved to infinity
    b = [K(i) for i in [2, 3, 5, 7, 11, 13, 17, 19]]
    moved = [inv(y - b[end]) for y in b[1:end-1]]
    F1 = RSM.thomae_theta_constants(b)
    F2 = RSM.thomae_theta_constants(moved)
    c0 = first(k for k in keys(F1) if !iszero(F1[k]))
    @test all(F1[c] * F2[c0] == F2[c] * F1[c0] for c in keys(F1))
    @test length(RSM.second_order_theta_constants(RSM.thomae_theta_constants(b; squares = true))) == 8
  end
end
