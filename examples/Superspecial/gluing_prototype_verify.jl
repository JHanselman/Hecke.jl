################################################################################
#
#  gluing_prototype_verify.jl : smoothness of a reconstructed genus 5 curve
#  (three quadrics in P^4) with Singular, in a separate environment:
#
#     julia --project=/path/to/env-with-Singular gluing_prototype_verify.jl curve.txt
#
#  curve.txt: the output of export_forms(quadrics) of gluing_prototype.jl,
#  written with println(io, export_forms(result.quadrics)). The field is
#  rebuilt from its defining polynomial (Singular over Nemo's FqField).
#
################################################################################

using Singular
import Singular.Nemo

function verify(data)
  p = data.characteristic
  Fp = Nemo.GF(p)
  Fpt, t = Nemo.polynomial_ring(Fp, "t")
  K, z = Nemo.finite_field(sum(Fp(c) * t^(i - 1) for (i, c) in enumerate(data.defining)), "z")
  R, x = Singular.polynomial_ring(K, ["x$i" for i in 1:5])
  elem(cs) = sum(K(c) * z^(i - 1) for (i, c) in enumerate(cs))
  Q = [sum(elem(cs) * prod(x[j]^e[j] for j in 1:5) for (e, cs) in form) for form in data.forms]
  I = Singular.std(Singular.Ideal(R, Q...))
  # the 3 x 3 minors of the Jacobian matrix: with I, the singular locus of the cone
  D = [[Singular.derivative(q, j) for j in 1:5] for q in Q]
  det3(c) = sum(sign * D[1][c[p1]] * D[2][c[p2]] * D[3][c[p3]]
                for (sign, (p1, p2, p3)) in ((1, (1, 2, 3)), (1, (2, 3, 1)), (1, (3, 1, 2)),
                                              (-1, (1, 3, 2)), (-1, (2, 1, 3)), (-1, (3, 2, 1))))
  minors = [det3(c) for c in ((i, j, k) for i in 1:5 for j in i+1:5 for k in j+1:5)]
  S = Singular.std(Singular.Ideal(R, Q..., minors...))
  # a smooth curve: the cone has dimension 2 and is singular only at its vertex
  cone, singular = Singular.dimension(I), Singular.dimension(S)
  return (cone_dimension = cone, singular_locus_dimension = singular, smooth_curve = cone == 2 && singular == 0)
end

verify_file(path::AbstractString) = verify(eval(Meta.parse(read(path, String))))

if abspath(PROGRAM_FILE) == @__FILE__
  println(verify_file(ARGS[1]))
end
