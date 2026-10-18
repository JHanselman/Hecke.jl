################################################################################
#
#  RiemannRelations.jl : Fay's and Riemann's relations between theta constants
#
#  Both are built on an Aronhold system a_1, ..., a_2g+1 (ThetaCharacteristics.jl)
#  with the characteristics L, lambda_h of Max Noether's construction; all
#  characteristics are doubled (integer vectors 2 * char, so no arithmetic in
#  QQ is needed).
#
#   - Fay's relations (frobenius_fay_relation of the development code): linear
#     relations between the gradients of the odd theta functions at 0 whose
#     coefficients are products of three theta constants. Only their
#     structure is computed here (fay_matrix_structure, _fay_relation_structure:
#     per relation the terms (column, coefficient, c1, c2, c3)); FayRelations.jl
#     evaluates them.
#   - Riemann's quartic relations, used to fix the signs of the Schottky-Jung
#     theta constants of the Prym (SignCorrection.jl): for a term (four even
#     characteristics with sum 0) and a symplectic matrix, the characteristics
#     and integral coefficients of a relation (_relation_terms_int); the
#     relation between the values is found by LLL (_relation_from_terms).
#
################################################################################

################################################################################
#
#  Fay's relations
#
################################################################################

# half_char_inner_prod for doubled characteristics
_doubled_inner(n::Vector{Int}, m::Vector{Int}, g::Int) = sum(n[i] * m[g + i] for i in 1:g)
_doubled_inner(n::Vector{Int}, g::Int) = _doubled_inner(n, n, g)
# the sign flip theta[c + 2l] = (-1)^(c' . l'') theta[c] for doubled characteristics
_doubled_flip(c::Vector{Int}, g::Int) = isodd(sum(c[i] * fld(c[g + i], 2) for i in 1:g)) ? -1 : 1
_doubled_key(c::Vector{Int}) = Tuple(mod.(c, 2))

# The w in GF(2)^2g with <rho, w> = 1 (symplectic)
function naive_non_orth_complement(rho::Vector{FqFieldElem})
  V = Iterators.product(repeat([[GF(2)(0),GF(2)(1)]], length(rho))...)
  result = Vector{FqFieldElem}[]
  for v in V
    v = collect(v)
    if half_char_inner_prod(rho, v) + half_char_inner_prod(v, rho) == 1
      push!(result, v)
    end
  end
  return result
end

# The terms (column, coefficient, c1, c2, c3) of the Fay relation of (w, rho)
# (here called rho and sigma, doubled): the coefficient of the gradient of
# theta[column] is coefficient * theta[c1] theta[c2] theta[c3].
function _fay_relation_structure(g::Int, rho::Vector{Int}, sigma::Vector{Int}, setup)
  a, a0, lambda, L, factor = setup
  hp(n) = _doubled_inner(n, g)
  hp(n, m) = _doubled_inner(n, m, g)
  flip(c) = _doubled_flip(c, g)
  terms = Tuple{Int, Int, NTuple{2*g, Int}, NTuple{2*g, Int}, NTuple{2*g, Int}}[]
  function add!(sign, base, v)
    # the term theta[base] theta[base + rho] grad theta[v or v + rho] theta[v + rho or v]
    s = sign * flip(base) * flip(base + rho) * flip(v) * flip(v + rho)
    if isodd(hp(v))
      push!(terms, (char_to_index(mod.(v, 2)), s, _doubled_key(base), _doubled_key(base + rho), _doubled_key(v + rho)))
    else
      push!(terms, (char_to_index(mod.(v + rho, 2)), s, _doubled_key(base), _doubled_key(base + rho), _doubled_key(v)))
    end
  end
  for h in 1:2^(g - 3)
    base = L + lambda[h]
    iszero(mod(hp(base + rho) - 1, 2)) && continue
    e = hp(lambda[h], lambda[h]) + hp(base + a0 + a[2*g]) + hp(rho + sigma, base)
    add!((-1)^e * factor, base, base + sigma)
  end
  for a_rho in [[a0]; a[1:7]], j in 1:2^(g - 4)
    base = L + lambda[j] + a_rho + a[2*g]
    iszero(mod(hp(base + rho) - 1, 2)) && continue
    e = hp(lambda[j] + a_rho, L) + hp(L, lambda[j] + a_rho) + hp(rho + sigma, base)
    add!(-(-1)^e, base, base + sigma)
  end
  return terms
end

# The data of the relations for the (doubled) Aronhold system a (default: the
# standard one): a, a_0 = sum a, the lambda_h, L and the common sign
_fay_setup(g::Int) = _fay_setup(g, [Int.(lift.(Ref(ZZ), av)) for av in aronhold_system(g)])

function _fay_setup(g::Int, a::Vector{Vector{Int}})
  a0 = sum(a)
  l = [a[2*p + 6] + a[2*p + 7] for p in 1:g - 3]
  lambda = [sum((v[p] * l[p] for p in 1:g - 3); init = zeros(Int, 2*g))
            for v in Iterators.product(ntuple(_ -> 0:1, g - 3)...)]
  lambda = vec(lambda)
  L = sum(a[i] for i in 8:2:2*g)
  isodd(g) && (L += a0)
  factor = (-1)^(_doubled_inner(L, a[2*g], g) + _doubled_inner(a[2*g], L, g))
  return (a, a0, lambda, L, factor)
end

@doc raw"""
    fay_matrix_structure(g, rho) -> Vector

Fay's relations for rho in GF(2)^2g (one for each w with <rho, w> = 1)
without the theta constants: per relation the terms (column, coefficient,
c1, c2, c3), see _fay_relation_structure.
"""
function fay_matrix_structure(g::Int, rho::Vector{FqFieldElem})
  @req g >= 4 "g needs to be bigger than 3."
  setup = _fay_setup(g)
  sigma = Int.(lift.(Ref(ZZ), rho))
  return [_fay_relation_structure(g, Int.(lift.(Ref(ZZ), w)), sigma, setup)
          for w in naive_non_orth_complement(rho)]
end

################################################################################
#
#  Riemann's relations (for the sign correction)
#
################################################################################

# The characteristic part of the Riemann relation of the term (four
# characteristics) for the symplectic matrix M1 (no theta constants): for
# each term of the relation the sorted indices of its four characteristics
# (`term_tup`), its integer coefficient including the sign flips (0 for a
# term with an odd characteristic) and the four characteristics reduced to
# bits (`keys`, the keys of the thetas).
function _relation_terms_int(g::Int, terms, M1::FqMatrix)
  t = [collect(Int, c) for c in terms]
  rho, sigma = t[1] + t[2], t[1] + t[3]
  a, a0, lambda, L, factor = _fay_setup(g, [Int.(lift.(Ref(ZZ), av)) for av in aronhold_system(g, M1)])
  hp(n) = _doubled_inner(n, g)
  hp(n, m) = _doubled_inner(n, m, g)
  term_tup = Vector{Int}[]
  term_coefficients = Int[]
  theta_keys = Vector{Vector{Int}}[]
  function add_term!(c, v1)
    chars = [v1, v1 + rho, v1 + sigma, v1 + sigma + rho]
    c *= mod(hp(chars[2]) - 1, 2) * prod(_doubled_flip(v, g) for v in chars)
    push!(term_coefficients, c)
    push!(theta_keys, [mod.(v, 2) for v in chars])
    push!(term_tup, sort([char_to_index(mod.(v, 2)) for v in chars]))
  end
  for h in 1:2^(g - 3)
    v1 = L + lambda[h]
    add_term!(factor * (-1)^(hp(lambda[h], lambda[h]) + hp(v1 + a0 + a[2*g]) + hp(rho + sigma, v1)), v1)
  end
  for a_rho in [[a0]; a[1:7]], j in 1:2^(g - 4)
    v1 = L + lambda[j] + a_rho + a[2*g]
    add_term!(-(-1)^(hp(lambda[j] + a_rho, L) + hp(L, lambda[j] + a_rho) + hp(rho + sigma, v1)), v1)
  end
  return (term_tup = term_tup, coefficients = term_coefficients, keys = theta_keys)
end

# The numerical part: the integral relation between the values of the terms
# (LLL); (false, ...) unless it has more than two terms and no term has a
# repeated characteristic. Two terms only when the other terms vanish (then
# Riemann's relation reduces to these two terms; otherwise a relation with
# two terms is spurious).
function _relation_from_terms(thetas, data)
  all(allunique, data.term_tup) || return false, [(Vector{Int64}[], ZZ(0))]
  CC = parent(first(values(thetas)))
  term_values = [c == 0 ? zero(CC) : c * prod(thetas[Tuple(k)] for k in ks)
                 for (c, ks) in zip(data.coefficients, data.keys)]
  # LLL only needs the digits that separate the terms (the relation has
  # coefficients +-1): the precision of the size range of the terms plus a
  # margin; the relation is then checked at full precision (full LLL if not)
  sol = _small_relation(term_values)
  result = filter(x -> x[2] != 0, collect(zip(data.term_tup, sol)))
  nonvanishing = count(v -> !contains_zero(v), term_values)
  length(result) > 2 || (length(result) == 2 && nonvanishing == 2) || return false, [(Vector{Int64}[], ZZ(0))]
  return true, sort!(result)
end

# The last row of integral_left_kernel of the values, computed at the
# precision of their size range + 128 bits instead of the full precision when
# the relation found there also holds at full precision.
function _small_relation(values::Vector{AcbFieldElem})
  CC = parent(values[1])
  exponent(z) = max(_arb_mid_2exp_rr(real(z)), _arb_mid_2exp_rr(imag(z)))
  nonzero = [exponent(v) for v in values if !iszero(v)]
  if length(nonzero) > 1
    low = (maximum(nonzero) - minimum(nonzero)) + 128
    if low < precision(CC) - 64
      # (under a lock: called from threads, and a new precision is a new
      # entry in the cache of fields, see _embedding_lock)
      CClow = lock(() -> AcbField(low), _embedding_lock)
      sol = integral_left_kernel(matrix(CClow.(values)))[1][end, :]
      total = sum((c * v for (c, v) in zip(sol, values)); init = zero(CC))
      count(!iszero, sol) > 2 && contains_zero(total) && return sol
    end
  end
  return integral_left_kernel(matrix(values))[1][end, :]
end

_arb_mid_2exp_rr(x::ArbFieldElem) = max(-(Int64(1) << 59),
  ccall((:arf_abs_bound_lt_2exp_si, Hecke.libflint), Int, (Ref{ArbFieldElem},), x))
