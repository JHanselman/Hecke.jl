@testset "Conics" begin

  @testset "Curves"
    C = @inferred conic_curve(QQ,[2,1,-5])

    @test @inferred genus(C) == 0
    @test @inferred base_field(C) == QQ
    @test @inferred discriminant(C) == -40
    
    Qxy, (x, y) = polynomial_ring(QQ, ["x", "y", "z"])
    @test @inferred equation(C) == 2*x^2 + y^2 - 5*z^2
    @test @inferred matrix(C) == matrix(ZZ, 3, 3, [2,0,0,0,1,0,0,0,-5])
  

    C = conic_curve(QQ,[1,2,-3, 3, -5, 7])

  end

  @testset "Points" begin
    C = conic_curve(QQ,[1,2,-3, 3, -5, 7])
    P = @inferred C([1,3,2])

    P = find_rational_point(C)
    
    C = conic_curve(QQ,[6,2,-3, 3, -9, 12])
    P = find_rational_point(C)

    C = @inferred conic_curve(QQ,[2,1,-5])
    @test_throws ErrorException find_rational_point(C)
  end
end
