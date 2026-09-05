

function azygetic_system(g::Int)
  zer = zero_matrix(GF(2), g, g)
  zer1 = zero_matrix(GF(2), g, 1)
	zer2 = zero_matrix(GF(2), g, 2)
	id = identity_matrix(GF(2), g)
	triang = zer
	for i in (1:g)
		for j in (i:g)
			triang[i,j] = 1
		end
	end

	odd_chars = [id; triang]
	even_chars = [[id zer2] ; [zer1 triang zer1]]

  return [odd_chars even_chars]
end

function aronhold_system(g::Int)
  azy_set = azygetic_system(g)

  zer = zero_matrix(GF(2), g, g)
	id = identity_matrix(GF(2), g)
	J = [zer id; id zer]
  J1 = [zer id; zer zer]

  w = diagonal(transpose(azy_set) * J1 * azy_set)

  for i in (1:2*g+2)
    e = zeros(GF(2),2*g+2)
    e[i] += g
    test, sol = can_solve_with_solution(J*azy_set, w+e)
    if test
      return [t + sol for t in [transpose(azy_set)[j,:] for j in (1:ncols(azy_set))][(1:end) .!= i]]
    end
  end

  error("Error in computation of aronhold system.")

end


function max_noether_relations(g::Int, thetas::Dict{NTuple{N, Int64}, AcbFieldElem}, rho::Vector{QQFieldElem}, sigma::Vector{QQFieldElem}) where N
  @req g >= 5 "g needs to be bigger than 4."
  a = aronhold_system(g)
  a = [QQ.(lift.(Ref(ZZ), av))/2 for av in a]
  a0 = sum(a)


  l = Vector{QQFieldElem}[]
  for p in (1:g-3)
    push!(l, a[2*p+6] + a[2*p+7])
  end

  lambda = Vector{QQFieldElem}[]
  l_M = matrix(l)
  V = Iterators.product(repeat([[QQ(0),QQ(1)]], g-3)...)
  for v in V 
    v = [v...]
    push!(lambda, v * l_M)
  end

  A = Vector{QQFieldElem}[]

  for lam in lambda
    for ai in [[a0] ; a[1:7]]
      push!(A, lam+ai)
    end
  end

  L = sum(a[i] for i in (8:2:2*g))
  if mod(g, 2) == 1
    L += a0
  end

  CC = parent(thetas[zeros(Int, 2*g)...])
  R, X = polynomial_ring(CC, 2^(2*g))


  D = thetas

  theta_indices = Hecke.theta_characteristics_indices(g)
  Dv = Dict([(theta_indices[i+1], X[i]) for i in (1:2^(2*g)-1)])
  Dv[zeros(Int, 2*g)...] = X[2^(2*g)]


  first_term = R(0)

  factor = (-1)^(half_char_inner_prod(L, a[2*g]) + half_char_inner_prod(a[2*g], L) )
 
  for h in (1:2^(g-3)) 
    first_term += (-1)^(half_char_inner_prod(lambda[h], lambda[h]) 
    + half_char_inner_prod(L+lambda[h] +a0 + a[2*g], L + lambda[h] + a0 + a[2*g])+half_char_inner_prod(rho+sigma, L + lambda[h])) * 
    theta_HI(D, L + lambda[h]) * theta_HI(D, L + lambda[h] + rho) *
    theta_HI(Dv, L + lambda[h] + sigma) * theta_HI(Dv, L + lambda[h] +rho + sigma)
  end

  first_term *= factor

  second_term = 0
  for a_rho in [[a0] ; a[1:7]]
    for j in (1:2^(g-4))
      second_term += (-1)^((half_char_inner_prod(lambda[j] + a_rho, L)  + half_char_inner_prod(L, lambda[j] +a_rho) + half_char_inner_prod(rho + sigma, L + lambda[j] + a_rho + a[2*g]))) *
      theta_HI(D, L + lambda[j] + a_rho + a[2*g]) * theta_HI(D, L + lambda[j] + a_rho + a[2*g] + rho) *
      theta_HI(Dv, L + lambda[j] + a_rho + a[2*g] + sigma) * theta_HI(Dv, L + lambda[j] + a_rho + a[2*g] + rho +sigma)
    end
  end

  return first_term - second_term
end

function _sign_flip(char::Vector{QQFieldElem})
  g = div(length(char), 2)
  v = [floor(QQFieldElem, c) for c in char]
  zer = zero_matrix(QQ, g, g)
  id = identity_matrix(QQ, g)
  J = [zer id; zer zer]
  result = (-1)^(Int(2*((transpose(char * J) * v))))
  return result
end


function theta_HI(D, char)
  newchar = mod.(Int.(2*char), Ref(2))
  return D[newchar...]*_sign_flip(char)
end

function half_char_inner_prod(n::Vector{QQFieldElem}, m::Vector{QQFieldElem})
  g = div(length(n),2)
  return Int(4*(transpose(n[1:g]) * m[g+1:2*g]))

end

function theta_list(thetas, g)
  theta_indices = Hecke.theta_characteristics_indices(g)
  theta_list = [thetas[theta_indices[i + 1]] for i in (1:2^(2*g)-1)]
  push!(theta_list, thetas[theta_indices[1]])
  return theta_list
end

function _construct_sparse_matrix(g, thetas)
  rho = zeros(QQ, 2*g)
  CC = parent(thetas[zeros(Int, 2*g)...])

  M = zero_matrix(CC, 2^(2*g), 2^(2*g));
  V = Iterators.product(repeat([[QQ(0),QQ(1//2)]], 2*g)...)
  k = 1

  for v in V
    sigma = collect(v)
    SS = max_noether_relations(g, thetas, rho, sigma)
    R = parent(SS)
    X = gens(R)
    ts = terms(SS)
    for t in ts
      c = t.coeffs[1]
      e = findfirst(!iszero, exponent_vector(t, 1))[1]
      M[k, e] = c
    end
    k += 1 
  end
  return M
end

function odd_theta_relations(g, thetas)
  M = _construct_sparse_matrix(g, thetas)
  even_indices = char_to_index.(even_theta_characteristics(g))
  odd_indices = char_to_index.(odd_theta_characteristics(g))
  M_even = M[:, even_indices]
  M_even_float = Complex{BigFloat}.(collect(M_even))
  K = permutedims(nullspace(transpose(M_even_float)))
  M_float = Complex{BigFloat}.(collect(M))

  CC = parent(thetas[zeros(Int, 2*g)...])
  R, X = polynomial_ring(CC, 2^(2*g))
  relations = zeros(R, nrows(K))

  tol = 10^(-50)

  for r in (1:10)#nrows(K))
    rel_vec = transpose(K[r,:]) * M_float
    for j in odd_indices
      if abs(rel[j]) > tol
        relations[r] += CC(rel[j]) * X[j]^2
      end 
    end 
  end

end