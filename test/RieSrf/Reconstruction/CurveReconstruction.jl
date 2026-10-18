# Generic, trigonal and plane quintic curves of genus 5 and 6 over QQ: the
# reconstructed canonical model vanishes on the differentials of the period
# matrix (exactly, in the function field). Long tests only (a period matrix
# of genus 5 or 6 and its Fay kernels take about a minute).
@testset "Reconstruction of curves of genus >= 5" begin
  if riesrf_long_tests()
    Hecke.Random.seed!(4711)
    vanish(forms, RS) = (ys = _differentials_in_function_field(RS)[2]; all(q -> iszero(evaluate(q, ys)), forms))

    # generic genus 5 with known quadrics
    curve = canonical_test_curve_g5()
    RS = RSM.riemann_surface(curve.plane, 400; superelliptic = false, model = :original)
    P = period_matrix_of_differentials(RS, curve.plane, curve.numerators)
    @test same_span(RSM.reconstruct_quadrics(P, QQ), curve.quadrics, 2)

    # trigonal genus 5: 3 quadrics (a scroll) and 2 cubics
    f = trigonal_test_curve()
    RS = RSM.riemann_surface(f, 400; superelliptic = false, model = :original)
    data = RSM.reconstruct_curve_data(RSM.small_period_matrix(RS))
    @test data.case === :trigonal && length(data.cubics) == 2
    model = RSM.reconstruct_curve(RSM.big_period_matrix(RS), QQ)
    @test length(model) == 5 && vanish(model, RS)

    # a plane quintic: its canonical model over QQ
    F = plane_quintic_test_curve()
    RS = RSM.riemann_surface(F, 500; superelliptic = false, model = :original)
    model = RSM.reconstruct_curve(RSM.big_period_matrix(RS), QQ)
    @test vanish(model, RS)
  end
end
