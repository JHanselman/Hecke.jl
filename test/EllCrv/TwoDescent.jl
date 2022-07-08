@testset "Two Descent of Elliptic Curves" begin
 
  @testset "Quartic invariants" begin 
    Rx, x = PolynomialRing(QQ, "x")
    q = x^4 +3*x^2 +2
    @test @inferred quartic_I_invariant(q) == 33
    @test @inferred quartic_J_invariant(q) == 378
    @test @inferred quartic_p_seminvariant(q) == -24
    @test @inferred quartic_q_seminvariant(q) == 16
    @test @inferred quartic_r_seminvariant(q) == 0
    @test @inferred quartic_g4_covariant(q) == -24*x^4 - 60*x^2 - 48
    @test @inferred quartic_g6_covariant(q) == -8*x^5 + 16*x
 
    q = 3*x^4 -5*x^3 +7*x^2 -12//13*x + 2
    @test @inferred quartic_I_invariant(q) == 1393//13
    @test @inferred quartic_J_invariant(q) == 204448//169
    @test @inferred quartic_p_seminvariant(q) == -93
    @test @inferred quartic_q_seminvariant(q) == -29385//13
    @test @inferred quartic_r_seminvariant(q) == 2971//13
    @test @inferred quartic_g4_covariant(q) == -93*x^4 - 956//13*x^3 - 1556//13*x^2 + 2784//13*x - 18496//169
    @test @inferred quartic_g6_covariant(q) == 2971//13*x^6 - 2530//13*x^5 - 12060//13*x^4 + 160360//169*x^3 - 195560//169*x^2 + 59344//169*x + 239680//2197

 
 end
 
end

