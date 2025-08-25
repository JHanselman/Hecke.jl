@testset "G2 Invariants" begin

    
    Qx, x = polynomial_ring(QQ, "x") 
    f1 = x^6+3*x+5
    h1 = x+2
    C = HyperellipticCurve(f1, h1)

    @test clebsch_invariants(C) == clebsch_invariants(f1, h1)
    @test weighted_equality(clebsch_invariants(C),[ QQ(192), QQ(6912032//1125), QQ(-221201408//1125), QQ(-5220510728192//3796875) ] ,[2,4,6,10])
    @test weighted_equality(igusa_clebsch_invariants(C),[ QQ(-23040), QQ(14930112), QQ(-106065874944), QQ(-374476383977472) ] ,[2,4,6,10])
    @test weighted_equality(igusa_invariants(C), [ QQ(-2880), QQ(190078), QQ(4428544), QQ(-12220963201), QQ(-91424898432) ] ,[2,4,6,8,10])
    @test g2_invariants(C) == [ QQ(171992678400000//79361891), QQ(563065344000//11337413), QQ(-31885516800//79361891) ]

    @test weighted_equality(igusa_clebsch_from_igusa(igusa_invariants(C)), igusa_clebsch_invariants(C), [2,4,6,10])
    @test weighted_equality(clebsch_from_igusa_clebsch(igusa_clebsch_invariants(C)), clebsch_invariants(C), [2,4,6,10])
    @test weighted_equality(igusa_from_g2(g2_invariants(C)), igusa_invariants(C), [2,4,6,8,10])


    F = GF(37)
    Fx, x = polynomial_ring(F, "x")

    f1 = x^5+8*x^4-5*x^3+3*x^2+7
    C = HyperellipticCurve(f1)
    @test weighted_equality(clebsch_invariants(C),[ F(9), F(18), F(26), F(24)] ,[2,4,6,10])
    @test weighted_equality(igusa_clebsch_invariants(C),[ QQ(-23040), QQ(14930112), QQ(-106065874944), QQ(-374476383977472) ] ,[2,4,6,10])
    @test weighted_equality(igusa_invariants(C), [ QQ(-2880), QQ(190078), QQ(4428544), QQ(-12220963201), QQ(-91424898432) ] ,[2,4,6,8,10])
    @test g2_invariants(C) == [ QQ(171992678400000//79361891), QQ(563065344000//11337413), QQ(-31885516800//79361891) ]


    @test weighted_equality(igusa_clebsch_from_igusa(igusa_invariants(C)), igusa_invariants(C), [2,4,6,10])
    @test weighted_equality(clebsch_from_igusa_clebsch(igusa_clebsch_invariants(C)), clebsch_invariants(C), [2,4,6,10])
    @test weighted_equality(igusa_from_g2(g2_invariants(C)), igusa_invariants(C), [2,4,6,8,10])


    F = GF(2, 4)
    a = gen(F)
    Fx, x = polynomial_ring(F, "x")

    f1 = x^6+a^2*x^5 + (a+a^3)*x^4+(a+1)*x^2+a*x+1
    C = HyperellipticCurve(f1, Fx(1))
    @test weighted_equality(igusa_invariants(C),[ F(0), F(0), F(0), F(1), F(a^12)] ,[2,4,6,8,10])
    @test g2_invariants(C) == [ F(0), F(0), F(a^9) ]
    @test weighted_equality(igusa_from_g2(g2_invariants(C)), igusa_invariants(C), [2,4,6,8,10])


    F = GF(5)
    Fx, x = polynomial_ring(F, "x")

    f1 = x^6+3*x^5-4*x^4+3*x^2+2*x-1
    C = HyperellipticCurve(f1)
    @test weighted_equality(igusa_clebsch_invariants(C),[ F(2), F(3), F(0), F(3) ] ,[2,4,6,10])
    @test weighted_equality(igusa_invariants(C),[ F(4), F(1), F(2), F(3), F(3)] ,[2,4,6,8,10])
    @test g2_invariants(C) == [ F(3), F(3), F(4) ]
    #@test weighted_equality(igusa_clebsch_from_igusa(igusa_invariants(C)), igusa_invariants(C), [2,4,6,10])
    @test weighted_equality(igusa_from_g2(g2_invariants(C)), igusa_invariants(C), [2,4,6,8,10])


    F = GF(7)
    Fx, x = polynomial_ring(F, "x")

    f1 = x^6+3*x^5-4*x^4+3*x^2+2*x-1
    C = HyperellipticCurve(f1)
    @test weighted_equality(clebsch_invariants(C),[ F(0), F(2), F(2), F(0)] ,[2,4,6,10])
    @test weighted_equality(igusa_clebsch_invariants(C),[ F(0), F(4), F(1), F(3) ] ,[2,4,6,10])
    @test weighted_equality(igusa_invariants(C),[ F(0), F(2), F(3), F(6), F(3)] ,[2,4,6,8,10])
    @test g2_invariants(C) == [ F(0), F(2), F(2) ]

    @test weighted_equality(igusa_clebsch_from_igusa(igusa_invariants(C)), igusa_invariants(C), [2,4,6,10])
    @test weighted_equality(clebsch_from_igusa_clebsch(igusa_clebsch_invariants(C)), clebsch_invariants(C), [2,4,6,10])
    @test weighted_equality(igusa_from_g2(g2_invariants(C)), igusa_invariants(C), [2,4,6,8,10])

    
  end