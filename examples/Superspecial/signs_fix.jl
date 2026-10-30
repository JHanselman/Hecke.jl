# fixed characteristics chosen among the nonvanishing even characteristics
function find_fixed_even_chars_nonvanishing(g::Int, thetas)
  F = GF(2)
  char_vecs = collect.(sort(RSM.even_theta_characteristics(g)))
  nonzero = [c for c in char_vecs if !iszero(thetas[Tuple(c)])]
  n = length(nonzero)
  dim = g * (2 * g + 1)
  flips = [[one(F) for _ in 1:n]]
  for v in basis(vector_space(F, dim))
    T_v = upper_triangular_matrix(v.v[1, :])
    push!(flips, [(transpose(c * T_v) * c) for c in nonzero])
  end
  E = echelon_form(matrix(flips))
  pivots = Int[]
  for j in 1:nrows(E)
    i = findfirst(i -> E[j, i] == one(F), 1:n)
    i === nothing || push!(pivots, i)
  end
  return [nonzero[i] for i in pivots], [nonzero[i] for i in 1:n if !(i in pivots)]
end

function correct_signs_exact2!(thetas, g::Int; pairs = RSM.load_sign_data(RSM._default_sign_data_file(g)),
                               max_tries::Int = 20000, rng = Random.MersenneTwister(7))
  fixed_thetas, non_fixed_thetas = find_fixed_even_chars_nonvanishing(g, thetas)
  S = RSM._SignSystem(g, RSM.char_to_index.(non_fixed_thetas))
  target = length(non_fixed_thetas)
  for (term, M1) in pairs
    S.rank >= target && break
    rel = exact_relation(thetas, term, RSM._relation_terms_int(g, term, M1))
    rel === nothing || RSM._add_relation!(S, rel)
  end
  tries = 0
  if S.rank < target
    F = GF(2)
    terms = RSM.find_zero_sum_tetrads(fixed_thetas)
    v1 = F.(ZZ.(RSM.max_noether_characteristics(g)[1] * 2))
    to_term = Dict{Any, FqMatrix}()
    while S.rank < target && tries < max_tries
      tries += 1
      term = terms[rand(rng, 1:length(terms))]
      M = get!(() -> RSM.map_even_characteristic(v1, F.(collect(term[1]))), to_term, term[1])
      M1 = random_isometry(g; rng = rng) * M
      rel = exact_relation(thetas, term, RSM._relation_terms_int(g, term, M1))
      rel === nothing || RSM._add_relation!(S, rel)
    end
  end
  RSM._apply_signs!(thetas, S, non_fixed_thetas)
  return thetas, S.rank, target, length(fixed_thetas)
end

# Relations with an arbitrary nonvanishing reference term: the equation of
# term i is (flips of term i) + (flips of the reference term) = [s_i s_t = -1]
function _add_relative_relation!(S, rel, reference)
  t = findfirst(x -> x[1] == reference, rel)
  t === nothing && return false
  st = rel[t][2]
  added = false
  for (mon, c) in rel
    cols = Dict{Int, Int}()
    for j in mon; cols[j] = get(cols, j, 0) + 1; end
    for j in reference; cols[j] = get(cols, j, 0) + 1; end
    odd = [j for (j, m) in cols if isodd(m)]
    added |= RSM._add_relation!(S, [(odd, c * st)])
  end
  return added
end

function correct_signs_exact3!(thetas, g::Int; pairs = RSM.load_sign_data(RSM._default_sign_data_file(g)),
                               max_tries::Int = 3000, extra_tries::Int = 5000, rng = Random.MersenneTwister(7))
  fixed_thetas, non_fixed_thetas = find_fixed_even_chars_nonvanishing(g, thetas)
  S = RSM._SignSystem(g, RSM.char_to_index.(non_fixed_thetas))
  target = length(non_fixed_thetas)
  F = GF(2)
  for (term, M1) in pairs
    S.rank >= target && break
    rel = exact_relation(thetas, term, RSM._relation_terms_int(g, term, M1))
    rel === nothing || RSM._add_relation!(S, rel)
  end
  v1 = F.(ZZ.(RSM.max_noether_characteristics(g)[1] * 2))
  to_term = Dict{Any, FqMatrix}()
  if S.rank < target
    terms = RSM.find_zero_sum_tetrads(fixed_thetas)
    tries = 0
    while S.rank < target && tries < max_tries
      tries += 1
      term = terms[rand(rng, 1:length(terms))]
      M = get!(() -> RSM.map_even_characteristic(v1, F.(collect(term[1]))), to_term, term[1])
      rel = exact_relation(thetas, term, RSM._relation_terms_int(g, term, random_isometry(g; rng = rng) * M))
      rel === nothing || RSM._add_relation!(S, rel)
    end
  end
  # any nonvanishing tetrad as the reference term
  if S.rank < target
    nonzero = [collect(c) for c in RSM.even_theta_characteristics(g) if !iszero(thetas[c])]
    nzset = Set(Tuple.(nonzero))
    tries = 0
    while S.rank < target && tries < extra_tries
      tries += 1
      c1, c2, c3 = nonzero[rand(rng, 1:end)], nonzero[rand(rng, 1:end)], nonzero[rand(rng, 1:end)]
      c4 = mod.(c1 + c2 + c3, 2)
      (Tuple(c4) in nzset && allunique([c1, c2, c3, c4])) || continue
      term = (c1, c2, c3, c4)
      M = get!(() -> RSM.map_even_characteristic(v1, F.(c1)), to_term, c1)
      data = RSM._relation_terms_int(g, term, random_isometry(g; rng = rng) * M)
      rel = exact_relation(thetas, term, data)
      rel === nothing && continue
      _add_relative_relation!(S, rel, sort([RSM.char_to_index(c) for c in term]))
    end
  end
  RSM._apply_signs!(thetas, S, non_fixed_thetas)
  return thetas, S.rank, target, length(fixed_thetas), S, non_fixed_thetas
end

# The sign flips (as lists of characteristics) spanning the solutions of the
# homogeneous system: one per free column
function sign_null_vectors(S, non_fixed_thetas)
  n = length(S.cols)
  free = setdiff(1:n, S.pivots)
  result = Vector{Vector{Any}}()
  for f in free
    x = falses(n)
    x[f] = true
    for k in S.rank:-1:1
      value = false
      for j in findall(S.rows[k])
        j == S.pivots[k] || (value ⊻= x[j])
      end
      x[S.pivots[k]] = value
    end
    push!(result, [non_fixed_thetas[j] for j in findall(x)])
  end
  return result
end

# The isomorphism key from the squares of the theta constants (theta^8 = (theta^2)^4)
function isomorphism_key_from_squares(squares, g::Int; n::Int = 8)
  eights = [squares[c]^4 for c in RSM.even_theta_characteristics(g)]
  I = [sum(e^k for e in eights) for k in 1:n]
  j0 = findfirst(!iszero, I)
  j0 === nothing && return "all zero"
  return join([string(j0); [string(divexact(I[j]^j0, I[j0]^j)) for j in 1:n]], "|")
end

# The kernel of the dual isogeny A/G -> A in the coordinates of the theta
# constants of A/G computed by glue_theta_squares: {(0, b)}
dual_kernel(g::Int) = [[k == g + i ? 1 : 0 for k in 1:2*g] for i in 1:g]

# Back along the dual isogeny: the key of A from the (signed) theta constants of A/G
back_key(F, thetas_child, g) = isomorphism_key_from_squares(glue_theta_squares([thetas_child], dual_kernel(g), F.zeta8)[1], g)
