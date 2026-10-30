################################################################################
#
#  verify_hit.jl : independent checks of a genus 5 Jacobian found by the
#  search (three quadrics in P^4, as written by export_forms in the
#  .jacobians files):
#
#     julia --project=/path/to/Hecke verify_hit.jl curve.txt
#
#  curve.txt: one line of a .jacobians file (the NamedTuple, not the "#" line).
#  Checks: complete intersection of degree 8 and genus 5, Hasse-Witt matrix
#  = 0 (superspecial), the smallest subfield containing the coefficients, and,
#  if the curve is defined over GF(p^2), #C(GF(p^2)) (maximal: p^2 + 1 + 10 p,
#  minimal: p^2 + 1 - 10 p) and the factorization of the discriminant of the
#  net of quadrics. Smoothness: gluing_prototype_verify.jl (Singular).
#
################################################################################

include(joinpath(@__DIR__, "superspecial.jl"))

function verify_hit(path::AbstractString; count_points::Bool = true)
  data = eval(Meta.parse(strip(read(path, String))))
  p = data.characteristic
  Fp = GF(p)
  Fpt, t = polynomial_ring(Fp, "t")
  K, z = finite_field(sum(Fp(c) * t^(i - 1) for (i, c) in enumerate(data.defining)), "z")
  R, x = polynomial_ring(K, ["x$i" for i in 1:5])
  elem(cs) = sum(K(c) * z^(i - 1) for (i, c) in enumerate(cs))
  Q = [sum(elem(cs) * prod(x[j]^e[j] for j in 1:5) for (e, cs) in form) for form in data.forms]
  println("complete intersection of degree 8, genus 5: ", complete_intersection_check(Q))
  HW = hasse_witt_matrix(Q)
  println("Hasse-Witt matrix zero (superspecial): ", iszero(HW), " (rank $(rank(HW)))")
  coefficients_all = reduce(vcat, [collect(coefficients(q)) for q in Q])
  dmin = first(d for d in 1:degree(K) if degree(K) % d == 0 && all(c -> c^(big(p)^d) == c, coefficients_all))
  println("coefficients in GF($p^$dmin)")
  dmin <= 2 || return
  k2, w = finite_field(p, 2, "w")
  emb = embed(k2, K)
  S, y = polynomial_ring(k2, ["y$i" for i in 1:5])
  Q2 = [sum(preimage(emb, c) * prod(y[j]^e[j] for j in 1:5)
            for (c, e) in zip(coefficients(q), Hecke.AbstractAlgebra.exponent_vectors(q))) for q in Q]
  println("model over GF($p^2):")
  foreach(q -> println("  ", q), Q2)
  D, fac = net_discriminant(Q2)
  println("discriminant of the net: factors of degrees ", [(total_degree(f), e) for (f, e) in fac])
  count_points || return Q2
  els = collect(k2)
  U, u = polynomial_ring(k2, "u")
  N = 0
  reps = [[[one(k2), a, b] for a in els for b in els]; [[zero(k2), one(k2), b] for b in els]; [[zero(k2), zero(k2), one(k2)]]]
  for r in reps, x4 in els
    polys = [evaluate(q, [U(r[1]), U(r[2]), U(r[3]), U(x4), u]) for q in Q2]
    h = gcd(gcd(polys[1], polys[2]), polys[3])
    N += iszero(h) ? length(els) : length(roots(h))
  end
  for v in [[[one(k2), zero(k2)]]; [[e, one(k2)] for e in els]]
    all(iszero(evaluate(q, [zero(k2), zero(k2), zero(k2), v[1], v[2]])) for q in Q2) && (N += 1)
  end
  println("#C(GF($p^2)) = $N (maximal $(p^2 + 1 + 10p), minimal $(p^2 + 1 - 10p))")
  return Q2
end

if abspath(PROGRAM_FILE) == @__FILE__
  verify_hit(ARGS[1])
end
