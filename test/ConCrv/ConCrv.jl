@testset "Conics" begin

  @testset "Curves"
    C = @inferred conic_curve(QQ,[2,1,-5])

    @test @inferred genus(C) == 0
    @test @inferred base_field(C) == QQ
    @test @inferred discriminant(C) == -40
    
    Qxy, (x, y) = polynomial_ring(QQ, ["x", "y", "z"])
    @test @inferred equation(C) == 2*x^2 + y^2 - 5*z^2
    @test @inferred matrix(C) == matrix(ZZ, 3, 3, [2,0,0,0,1,0,0,0,-5])
  

  end

  @testset "Points" begin
    C = conic_curve(QQ,[1,2,-3, 3, -5, 7])
    P = @inferred C([1,3,2])

    P = find_rational_point(C)
    
    C = conic_curve(QQ,[6,2,-3, 3, -9, 12])
    P = find_rational_point(C)

    C = @inferred conic_curve(QQ,[2,1,-5])
    @test_throws ErrorException find_rational_point(C)


    K, a = cyclotomic_field(10)
    C = conic_curve(K,[1,a,-3, 3, -5, 7])
    P = find_rational_point(C)

    kt, t = rational_function_field(QQ, "t")
    C = conic_curve(kt, [1, 2 +2*t - t^2, -3 - 4*t + 8*t^2 + 16*t^3 - 48*t^4])
    P = find_rational_point(C)
    #f(x+z, y-2*x, z-3*y+x)

    R, (x,y,z) = polynomial_ring(kt, ["x","y","z"])
    g = (-48*t^4 + 16*t^3 + 4*t^2 + 4*t + 6)*x^2 + (288*t^4 - 96*t^3 - 44*t^2 +
    16*t + 10)*x*y + (-96*t^4 + 32*t^3 + 16*t^2 - 8*t - 4)*x*z + (-432*t^4 +
    144*t^3 + 71*t^2 - 34*t - 25)*y^2 + (288*t^4 - 96*t^3 - 48*t^2 + 24*t +
    18)*y*z + (-48*t^4 + 16*t^3 + 8*t^2 - 4*t - 2)*z^2
    C = conic_curve(g)
    P = find_rational_point(C)

    
    kt, t = rational_function_field(GF(37), "t")
    C = conic_curve(kt, [t^2 + 1, 3*t^2+2, 2*t^3 - 10*t^2 +2*t -9])
    P = find_rational_point(C)

  end

    @testset "Models" begin

  end

end
