################################################################################
#
#  Accola's and FGSM's equations in genus 5 (development code, Main)
#
#  Ported from Theta.jl (Agostini-Chua: accola.jl, fgsm.jl), same
#  characteristics. Theta.jl evaluates every theta constant separately and
#  takes the minimum of |r_1 +- ... +- r_k| over the signs; here all theta
#  constants come from one acb_theta_all call (a dictionary) and each relation
#  is the product over the signs (r_1 fixed), the polynomial in the squares
#  r_i^2 (products of 8 theta constants) that does not depend on the branches
#  of the square roots: holomorphic in tau, so Newton applies. Degrees in the
#  theta constants: 32 (Accola, 4 roots, 8 signs), 128 (FGSM, 6 roots, 32
#  signs). Needs SchottkySampling.jl (theta_equation_system).
#
################################################################################

_theta_key(c) = Tuple(mod.(vcat(c[1], c[2]), 2))

_coset_sum(cs) = [mod.(sum(c[1] for c in cs), 2), mod.(sum(c[2] for c in cs), 2)]

# The 8 characteristics e + <g1, g2, g3>.
function _coset_keys(e, g1, g2, g3)
  zero_char = [0 * e[1], 0 * e[2]]
  return [_theta_key(e + s) for s in (zero_char, g1, g2, g3, g1 + g2, g1 + g3, g2 + g3, g1 + g2 + g3)]
end

@doc raw"""
    accola_characteristics() -> Vector{Vector{Vector{NTuple{10, Int}}}}

The characteristics of Accola's 8 special theta relations (Theta.jl's
accola_chars): for each relation 4 cosets e + <g1, g2, g3> of 8
characteristics each.
"""
function accola_characteristics()
  base = [[[1,0,0,0,0],[0,0,0,0,0]],
           [[0,1,0,0,0],[1,0,0,0,0]],
           [[0,0,1,0,0],[1,1,0,0,0]],
           [[0,0,0,1,0],[1,1,1,0,0]],
           [[0,0,0,0,1],[1,1,1,1,0]],
           [[1,0,0,0,0],[0,1,1,1,1]],
           [[0,1,0,0,0],[0,0,1,1,1]],
           [[0,0,1,0,0],[0,0,0,1,1]],
           [[0,0,0,1,0],[0,0,0,0,1]],
           [[1,1,1,1,0],[0,1,0,1,0]],
           [[1,1,1,1,0],[1,0,1,0,1]]]
  index_sets = [[[1,2,3,4], [5,6,7,8], [5,6,9,10], [5,7,9,11]], #SR1234
                      [[1,2,3,5], [4,6,7,8], [4,6,9,10], [4,7,9,11]], #SR1235
                      [[1,2,3,6], [5,4,7,8], [5,4,9,10], [5,7,9,11]], #SR1236
                      [[1,2,3,7], [5,6,4,8], [5,6,9,10], [5,4,9,11]], #SR1237
                      [[1,2,3,8], [5,6,7,4], [5,6,9,10], [5,7,9,11]], #SR1238
                      [[1,2,3,9], [5,6,7,8], [5,6,4,10], [5,7,4,11]], #SR1239
                      [[1,2,3,10], [5,6,7,8], [5,6,9,4], [5,7,9,11]], #SR12310
                      [[1,2,3,11], [5,6,7,8], [5,6,9,10], [5,7,9,4]]] #SR12311
  relations = Vector{Vector{Vector{NTuple{10, Int}}}}()
  for indices in index_sets
    g1, g2, g3 = (_coset_sum([base[i] for i in indices[k]]) for k in 2:4)
    push!(relations, [_coset_keys(base[i], g1, g2, g3) for i in (1, 2, 3, indices[1][4])])
  end
  return relations
end

@doc raw"""
    fgsm_characteristics() -> Vector{Vector{Vector{NTuple{10, Int}}}}

The characteristics of the FGSM relations S_34, S_35, S_45 in genus 5
(Theta.jl's fgsm_chars): for each relation 6 sets of 8 characteristics.
"""
function fgsm_characteristics()
  fgsm_34 = [[[[0,0,0,0,0], [0,0,0,0,0]],
               [[0,0,0,0,0], [1,1,1,1,1]],
               [[0,0,1,1,0], [0,1,0,0,0]],
               [[0,0,1,1,0], [1,0,1,1,1]],
               [[1,1,0,0,0], [0,0,0,1,0]],
               [[1,1,0,0,0], [1,1,1,0,1]],
               [[1,1,1,1,0], [0,1,0,1,0]],
               [[1,1,1,1,0], [1,0,1,0,1]]],
              [[[1,0,1,0,0], [0,0,0,0,0]],
               [[1,0,1,0,0], [1,1,1,1,1]],
               [[1,0,0,1,0], [0,1,0,0,0]],
               [[1,0,0,1,0], [1,0,1,1,1]],
               [[0,1,1,0,0], [0,0,0,1,0]],
               [[0,1,1,0,0], [1,1,1,0,1]],
               [[0,1,0,1,0], [0,1,0,1,0]],
               [[0,1,0,1,0], [1,0,1,0,1]]],
              [[[0,0,0,0,0], [0,0,1,1,0]],
               [[0,0,0,0,0], [1,1,0,0,1]],
               [[0,0,1,1,0], [0,1,1,1,0]],
               [[0,0,1,1,0], [1,0,0,0,1]],
               [[1,1,0,0,0], [0,0,1,0,0]],
               [[1,1,0,0,0], [1,1,0,1,1]],
               [[1,1,1,1,0], [0,1,1,0,0]],
               [[1,1,1,1,0], [1,0,0,1,1]]],
              [[[1,0,0,0,1], [0,0,0,0,0]],
               [[1,0,0,0,1], [1,1,1,1,1]],
               [[1,0,1,1,1], [0,1,0,0,0]],
               [[1,0,1,1,1], [1,0,1,1,1]],
               [[0,1,0,0,1], [0,0,0,1,0]],
               [[0,1,0,0,1], [1,1,1,0,1]],
               [[0,1,1,1,1], [0,1,0,1,0]],
               [[0,1,1,1,1], [1,0,1,0,1]]],
              [[[0,0,1,0,1], [0,0,0,0,0]],
               [[0,0,1,0,1], [1,1,1,1,1]],
               [[0,0,0,1,1], [0,1,0,0,0]],
               [[0,0,0,1,1], [1,0,1,1,1]],
               [[1,1,1,0,1], [0,0,0,1,0]],
               [[1,1,1,0,1], [1,1,1,0,1]],
               [[1,1,0,1,1], [0,1,0,1,0]],
               [[1,1,0,1,1], [1,0,1,0,1]]],
              [[[1,0,0,0,1], [0,0,1,1,0]],
               [[1,0,0,0,1], [1,1,0,0,1]],
               [[1,0,1,1,1], [0,1,1,1,0]],
               [[1,0,1,1,1], [1,0,0,0,1]],
               [[0,1,0,0,1], [0,0,1,0,0]],
               [[0,1,0,0,1], [1,1,0,1,1]],
               [[0,1,1,1,1], [0,1,1,0,0]],
               [[0,1,1,1,1], [1,0,0,1,1]]]]
  fgsm_35 = [[[[0,0,0,0,0], [0,0,0,0,0]],
               [[0,0,0,0,0], [1,1,1,1,1]],
               [[0,0,1,0,1], [0,1,0,0,0]],
               [[0,0,1,0,1], [1,0,1,1,1]],
               [[1,1,0,0,0], [0,0,0,0,1]],
               [[1,1,0,0,0], [1,1,1,1,0]],
               [[1,1,1,0,1], [0,1,0,0,1]],
               [[1,1,1,0,1], [1,0,1,1,0]]],
              [[[1,0,1,0,0], [0,0,0,0,0]],
               [[1,0,1,0,0], [1,1,1,1,1]],
               [[1,0,0,0,1], [0,1,0,0,0]],
               [[1,0,0,0,1], [1,0,1,1,1]],
               [[0,1,1,0,0], [0,0,0,0,1]],
               [[0,1,1,0,0], [1,1,1,1,0]],
               [[0,1,0,0,1], [0,1,0,0,1]],
               [[0,1,0,0,1], [1,0,1,1,0]]],
              [[[0,0,0,0,0], [0,0,1,0,1]],
               [[0,0,0,0,0], [1,1,0,1,0]],
               [[0,0,1,0,1], [0,1,1,0,1]],
               [[0,0,1,0,1], [1,0,0,1,0]],
               [[1,1,0,0,0], [0,0,1,0,0]],
               [[1,1,0,0,0], [1,1,0,1,1]],
               [[1,1,1,0,1], [0,1,1,0,0]],
               [[1,1,1,0,1], [1,0,0,1,1]]],
              [[[1,0,0,1,0], [0,0,0,0,0]],
               [[1,0,0,1,0], [1,1,1,1,1]],
               [[1,0,1,1,1], [0,1,0,0,0]],
               [[1,0,1,1,1], [1,0,1,1,1]],
               [[0,1,0,1,0], [0,0,0,0,1]],
               [[0,1,0,1,0], [1,1,1,1,0]],
               [[0,1,1,1,1], [0,1,0,0,1]],
               [[0,1,1,1,1], [1,0,1,1,0]]],
              [[[0,0,1,1,0], [0,0,0,0,0]],
               [[0,0,1,1,0], [1,1,1,1,1]],
               [[0,0,0,1,1], [0,1,0,0,0]],
               [[0,0,0,1,1], [1,0,1,1,1]],
               [[1,1,1,1,0], [0,0,0,0,1]],
               [[1,1,1,1,0], [1,1,1,1,0]],
               [[1,1,0,1,1], [0,1,0,0,1]],
               [[1,1,0,1,1], [1,0,1,1,0]]],
              [[[1,0,0,1,0], [0,0,1,0,1]],
               [[1,0,0,1,0], [1,1,0,1,0]],
               [[1,0,1,1,1], [0,1,1,0,1]],
               [[1,0,1,1,1], [1,0,0,1,0]],
               [[0,1,0,1,0], [0,0,1,0,0]],
               [[0,1,0,1,0], [1,1,0,1,1]],
               [[0,1,1,1,1], [0,1,1,0,0]],
               [[0,1,1,1,1], [1,0,0,1,1]]]]
  fgsm_45 = [[[[0,0,0,0,0], [0,0,0,0,0]],
               [[0,0,0,0,0], [1,1,1,1,1]],
               [[0,0,0,1,1], [0,1,0,0,0]],
               [[0,0,0,1,1], [1,0,1,1,1]],
               [[1,1,0,0,0], [0,0,0,0,1]],
               [[1,1,0,0,0], [1,1,1,1,0]],
               [[1,1,0,1,1], [0,1,0,0,1]],
               [[1,1,0,1,1], [1,0,1,1,0]]],
              [[[1,0,0,1,0], [0,0,0,0,0]],
               [[1,0,0,1,0], [1,1,1,1,1]],
               [[1,0,0,0,1], [0,1,0,0,0]],
               [[1,0,0,0,1], [1,0,1,1,1]],
               [[0,1,0,1,0], [0,0,0,0,1]],
               [[0,1,0,1,0], [1,1,1,1,0]],
               [[0,1,0,0,1], [0,1,0,0,1]],
               [[0,1,0,0,1], [1,0,1,1,0]]],
              [[[0,0,0,0,0], [0,0,0,1,1]],
               [[0,0,0,0,0], [1,1,1,0,0]],
               [[0,0,0,1,1], [0,1,0,1,1]],
               [[0,0,0,1,1], [1,0,1,0,0]],
               [[1,1,0,0,0], [0,0,0,1,0]],
               [[1,1,0,0,0], [1,1,1,0,1]],
               [[1,1,0,1,1], [0,1,0,1,0]],
               [[1,1,0,1,1], [1,0,1,0,1]]],
              [[[1,0,1,0,0], [0,0,0,0,0]],
               [[1,0,1,0,0], [1,1,1,1,1]],
               [[1,0,1,1,1], [0,1,0,0,0]],
               [[1,0,1,1,1], [1,0,1,1,1]],
               [[0,1,1,0,0], [0,0,0,0,1]],
               [[0,1,1,0,0], [1,1,1,1,0]],
               [[0,1,1,1,1], [0,1,0,0,1]],
               [[0,1,1,1,1], [1,0,1,1,0]]],
              [[[0,0,1,1,0], [0,0,0,0,0]],
               [[0,0,1,1,0], [1,1,1,1,1]],
               [[0,0,1,0,1], [0,1,0,0,0]],
               [[0,0,1,0,1], [1,0,1,1,1]],
               [[1,1,1,1,0], [0,0,0,0,1]],
               [[1,1,1,1,0], [1,1,1,1,0]],
               [[1,1,1,0,1], [0,1,0,0,1]],
               [[1,1,1,0,1], [1,0,1,1,0]]],
              [[[1,0,1,0,0], [0,0,0,1,1]],
               [[1,0,1,0,0], [1,1,1,0,0]],
               [[1,0,1,1,1], [0,1,0,1,1]],
               [[1,0,1,1,1], [1,0,1,0,0]],
               [[0,1,1,0,0], [0,0,0,1,0]],
               [[0,1,1,0,0], [1,1,1,0,1]],
               [[0,1,1,1,1], [0,1,0,1,0]],
               [[0,1,1,1,1], [1,0,1,0,1]]]]
  return [[[_theta_key(c) for c in s] for s in S] for S in (fgsm_34, fgsm_35, fgsm_45)]
end

# The square roots r_i of the products of the theta constants over the sets.
_root_products(thetas, sets) = [sqrt(prod(thetas[k] for k in s)) for s in sets]

# The signed sums r_1 +- r_2 +- ... +- r_k (2^(k-1) of them).
function _signed_sums(r::Vector{AcbFieldElem})
  k = length(r)
  sums = AcbFieldElem[]
  for bits in 0:2^(k - 1) - 1
    s = r[1]
    for i in 2:k
      isodd(bits >> (i - 2)) ? (s -= r[i]) : (s += r[i])
    end
    push!(sums, s)
  end
  return sums
end

@doc raw"""
    signed_root_relations(thetas, relations, state = nothing; minimum = false)
      -> (Vector{AcbFieldElem}, Vector{Int})

For each relation (a list of k sets of characteristics) the product over the
signs of r_1 +- ... +- r_k, r_i the square root of the product s_i of the
theta constants over the i-th set (a polynomial in the theta constants,
independent of the branches), divided by s_j^(2^(k-2)) for the root r_j of
largest absolute value (j from `state` if given, so that the normalization
is fixed while the Jacobian is computed): a scale of the size of the terms,
as the theta constants of a reduced matrix have very different sizes. With
`minimum = true` instead the signed sum of smallest absolute value divided
by |r_j| (Theta.jl's diagnostic, normalized; not holomorphic).
"""
function signed_root_relations(thetas, relations, state = nothing; minimum::Bool = false)
  values = AcbFieldElem[]
  choices = Int[]
  for (n, sets) in enumerate(relations)
    k = length(sets)
    squares = [prod(thetas[c] for c in s) for s in sets]
    r = [sqrt(x) for x in squares]
    j = state === nothing ? argmax([RSR._abs64(x) for x in squares]) : state[n]
    sums = _signed_sums(r)
    push!(values, minimum ? sums[argmin([RSR._abs64(x) for x in sums])] / r[j] :
                            prod(sums) / squares[j]^(2^(k - 2)))
    push!(choices, j)
  end
  return values, choices
end

# The signed sum r_1 +- ... +- r_k with the signs of _signed_sums[bits + 1].
function _signed_sum(r::Vector{AcbFieldElem}, bits::Int)
  s = r[1]
  for i in 2:length(r)
    isodd(bits >> (i - 2)) ? (s -= r[i]) : (s += r[i])
  end
  return s
end

@doc raw"""
    sign_pattern_relations(thetas, relations, state = nothing) -> (Vector{AcbFieldElem}, state)

For each relation the signed sum r_1 +- ... +- r_k of smallest absolute
value (the factor of the product in signed_root_relations that vanishes on
the locus nearby), divided by the root r_j of largest absolute value. The
state fixes per relation the signs, j and the branches of the square roots
(the ones closest to the roots where the state was made), so that the
values are holomorphic near that point: a system of degree 4 (relative)
instead of the products of 8 or 32 factors, with far fewer spurious local
minima of the residual.
"""
function sign_pattern_relations(thetas, relations, state = nothing)
  values = AcbFieldElem[]
  new_state = Tuple{Int, Int, Vector{ComplexF64}}[]
  for (n, sets) in enumerate(relations)
    roots = [sqrt(prod(thetas[c] for c in s)) for s in sets]
    if state === nothing
      bits = argmin([RSR._abs64(x) for x in _signed_sums(roots)]) - 1
      j = argmax([RSR._abs64(x) for x in roots])
      references = [RSR._c64(x) for x in roots]
    else
      bits, j, references = state[n]
      for i in eachindex(roots)
        c = RSR._c64(roots[i])
        abs(c - references[i]) > abs(c + references[i]) && (roots[i] = -roots[i])
      end
    end
    push!(values, _signed_sum(roots, bits) / roots[j])
    push!(new_state, (bits, j, references))
  end
  return values, new_state
end

_relation_residual(relations, product::Bool) =
  product ? (g, thetas, state) -> signed_root_relations(thetas, relations, state) :
            (g, thetas, state) -> sign_pattern_relations(thetas, relations, state)

@doc raw"""
    accola_system(; product = false, transforms = nothing) -> ThetaEquationSystem

Accola's 8 special theta relations as a system for sample_schottky_locus:
by default locally the vanishing signed sums (sign_pattern_relations), with
`product = true` the polynomials of degree 32 (signed_root_relations).
"""
function accola_system(; product::Bool = false, transforms = nothing)
  return ThetaEquationSystem(product ? "accola_product" : "accola",
                             _relation_residual(accola_characteristics(), product),
                             transforms === nothing ? ZZMatrix[] : collect(transforms))
end

@doc raw"""
    fgsm_system(; product = false, transforms = nothing) -> ThetaEquationSystem

The FGSM relations S_34, S_35, S_45 as a system for sample_schottky_locus:
by default locally the vanishing signed sums (sign_pattern_relations), with
`product = true` the polynomials of degree 128 (signed_root_relations).
"""
function fgsm_system(; product::Bool = false, transforms = nothing)
  return ThetaEquationSystem(product ? "fgsm_product" : "fgsm",
                             _relation_residual(fgsm_characteristics(), product),
                             transforms === nothing ? ZZMatrix[] : collect(transforms))
end

@doc raw"""
    schottky_equation_values(tau) -> NamedTuple

log2 of the largest normalized residual at tau of the Accola and FGSM
systems (signed sums and products), and of Theta.jl's diagnostics (over the relations the largest
normalized smallest signed sum).
"""
function schottky_equation_values(tau::AcbMatrix)
  g = nrows(tau)
  @req g == 5 "Accola's and FGSM's equations are for genus 5."
  CC = base_ring(tau)
  thetas = Hecke.thetas([zero(CC) for _ in 1:g], tau)
  log2max(v) = round(_max_log2(v), digits = 1)
  residual(S) = log2max(first(_system_residual(S, tau)))
  return (accola = residual(accola_system()), fgsm = residual(fgsm_system()),
          accola_product = residual(accola_system(product = true)),
          fgsm_product = residual(fgsm_system(product = true)),
          accola_minimum = log2max(first(signed_root_relations(thetas, accola_characteristics(); minimum = true))),
          fgsm_minimum = log2max(first(signed_root_relations(thetas, fgsm_characteristics(); minimum = true))))
end
