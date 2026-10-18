################################################################################
#
#  Generation/OscarIsometries.jl : random isometries for the sign data search
#
#  The random search for Riemann relations (find_sign_data, and the fallback
#  of correct_signs_with_data! when the stored sign data do not suffice)
#  needs random elements of the orthogonal group O(g, g) over GF(2) (the
#  isometries of the quadratic form x'y). Hecke has no such groups; this file
#  provides them with Oscar. It is not part of the package: include it after
#  `using Oscar`:
#
#    using Oscar
#    include(joinpath(dirname(pathof(Hecke)), "RieSrf", "Reconstruction", "Generation", "OscarIsometries.jl"))
#    pairs = Hecke.RiemannSurfaces.find_sign_data(g, thetas)
#    Hecke.RiemannSurfaces.save_sign_data("SignDataG$(g).txt", pairs)
#
################################################################################

Hecke.RiemannSurfaces._set_random_isometry_sampler!(function (g::Int)
  F = GF(2)
  form = [zero_matrix(F, g, g) identity_matrix(F, g); zero_matrix(F, g, g) zero_matrix(F, g, g)]
  G = isometry_group(quadratic_form(form))
  return () -> matrix(rand(G))
end)
