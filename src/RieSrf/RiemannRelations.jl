#=
using Hecke.RiemannSurfaces
using GenericLinearAlgebra
R, (x,y) = polynomial_ring(QQ, [:x,:y])
f = 2*x^5*y^3 + 5*x^4*y^3 - 9*x^4*y^2 + 3*x^3*y - 4*x^2*y^2 - 3*x*y^3 + 1
RS = riemann_surface(f, 200, integration_method = "heuristic")
g = genus(RS)
tau = small_period_matrix(RS)
CC = complex_field(RS)
z = zeros(CC, 5)
thetas = Hecke.thetas(z, tau)

z0 = CC.([1.4,0,3.3,1//2,1])
thetas5_z0 = Hecke.thetas(z0, tau)
Th_sq = map(x->x^2, theta_list(thetas5_z0, 5))


A = aronhold_system(g, azygetic_system(g))
A2 = aronhold_system(g, azygetic_system_flip(g))

I1 = collect((20:2^(2*g-1)))
I2 = collect((14:2^(2*g-1)))

M1 = theta_square_relations(g, thetas, A, I1);
M2 = theta_square_relations(g, thetas, A2, I2);
M = [M1 ; M2];
even_indices = char_to_index.(even_theta_characteristics(g))
odd_indices = char_to_index.(odd_theta_characteristics(g))
M_even = M[:, even_indices];

CC = parent(thetas[zeros(Int, 2*g)...])
prec = precision(CC)
setprecision(BigFloat, prec)
M_even_float = Complex{Float64}.(collect(M_even));
M_even_float = (x-> abs(x) < 10^(-50) ? zero(ComplexF64) : x).(M_even_float);
K = permutedims(nullspace(transpose(M_even_float)));
M_float = Complex{Float64}.(collect(M));
O = K*(M_float[:,odd_indices])
rank(O)

#Sanity check:
P = M * Th_sq;
length(filter( x -> abs(x) > 10^(-30), P)) == 0

=#

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

function azygetic_system_flip(g::Int)
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

  odd_chars = [triang; id]
	even_chars = [[zer1 triang zer1] ; [id zer2] ]
  return [odd_chars even_chars]
end


function aronhold_system(g::Int, azy_set)

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


function theta_square_relations(g::Int, thetas::Dict{NTuple{N, Int64}, AcbFieldElem}) where N
  return theta_square_relations(g, thetas, collect(1:2^(2*g)))
end

function theta_square_relations(g::Int, thetas::Dict{NTuple{N, Int64}, AcbFieldElem},a,  indices::Vector{Int}) where N
  @req g >= 5 "g needs to be bigger than 4."
  a = [GF(2).(av) for av in a]
  a0 = sum(a)


  l = Vector{FqFieldElem}[]
  for p in (1:g-3)
    push!(l, a[2*p+6] + a[2*p+7])
  end

  lambda = Vector{FqFieldElem}[]
  l_M = matrix(l)
  V = Iterators.product(repeat([[GF(2)(0),GF(2)(1)]], g-3)...)
  for v in V 
    v = [v...]
    push!(lambda, v * l_M)
  end

  A = Vector{FqFieldElem}[]

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


  D = Dict([(collect(GF(2).(v)), thetas[v]) for v in keys(thetas)])

  theta_indices_temp = Hecke.theta_characteristics_indices(g)
  theta_indices = theta_indices_temp[2:end]
  push!(theta_indices, theta_indices_temp[1])

  Dv = Dict([(collect(GF(2).(theta_indices[i])), i) for i in (1:2^(2*g))])

  M = zero_matrix(CC, length(indices), 2^(2*g));

  for v in (1:length(indices))
    V = indices[v]
    sigma = GF(2).(collect(theta_indices[V]))

    factor = (-1)^(half_char_inner_prod(L, a[2*g]) + half_char_inner_prod(a[2*g], L) )
  
    for h in (1:2^(g-3)) 
      first_term = (-1)^(half_char_inner_prod(lambda[h], lambda[h]) 
      + half_char_inner_prod(L+lambda[h] +a0 + a[2*g], L + lambda[h] + a0 + a[2*g])+half_char_inner_prod(sigma, L + lambda[h])) * 
      D[L + lambda[h]]^2 
      j = Dv[L + lambda[h] + sigma]
      M[v, j] += first_term *factor
    end

    for a_rho in [[a0] ; a[1:7]]
      for j in (1:2^(g-4))
        second_term = (-1)^((half_char_inner_prod(lambda[j] + a_rho, L)  + half_char_inner_prod(L, lambda[j] +a_rho) + half_char_inner_prod(sigma, L + lambda[j] + a_rho + a[2*g]))) *
        D[L + lambda[j] + a_rho + a[2*g]]^2
        t = Dv[ L + lambda[j] + a_rho + a[2*g] + sigma]
        M[v, t] -= second_term
      end
    end
  end

  return M
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

function half_char_inner_prod(n::Vector{FqFieldElem}, m::Vector{FqFieldElem})
  g = div(length(n),2)
  return Int(lift(ZZ,((transpose(n[1:g]) * m[g+1:2*g]))))
end

function theta_list(thetas, g)
  theta_indices = Hecke.theta_characteristics_indices(g)
  theta_list = [thetas[theta_indices[i + 1]] for i in (1:2^(2*g)-1)]
  push!(theta_list, thetas[theta_indices[1]])
  return theta_list
end

function _construct_sparse_matrix(g, thetas)
  CC = parent(thetas[zeros(Int, 2*g)...])
  rho = zeros(QQ, 2*g)

  N = 2^(2*g-1)

  M = zero_matrix(CC, N, 2^(2*g));
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
    if k == N
      break
    end
    k += 1 
    println(k)
  end
  return M
end

function odd_theta_relations(g, thetas)
  M = _construct_sparse_matrix(g, thetas)
  even_indices = char_to_index.(even_theta_characteristics(g))
  odd_indices = char_to_index.(odd_theta_characteristics(g))
  M_even = @view M[:, even_indices]

  CC = parent(thetas[zeros(Int, 2*g)...])
  prec = precision(CC)
  setprecision(BigFloat, prec)
  #M_even_float = Complex{BigFloat}.(collect(M_even))
  M_even_float = Complex{Float64}.(collect(M_even))
  M_even_float = (x-> abs(x) < 10^(-50) ? zero(ComplexF64) : x).(M_even_float)
  K = permutedims(nullspace(transpose(M_even_float)))
  M_float = Complex{Float64}.(collect(M))

  CC = parent(thetas[zeros(Int, 2*g)...])
  R, X = polynomial_ring(CC, 2^(2*g))
  return K*(M_float[:,odd_indices])
end

function odd_theta_relations_2(g, thetas)
  A = aronhold_system(g, azygetic_system(g))
  A2 = aronhold_system(g, azygetic_system_flip(g))

  I1 = collect((20:2^(2*g-1)))
  I2 = collect((14:2^(2*g-1)))

  M1 = theta_square_relations(g, thetas, A, I1);
  M2 = theta_square_relations(g, thetas, A2, I2);
  M = [M1 ; M2];
  even_indices = char_to_index.(even_theta_characteristics(g))
  odd_indices = char_to_index.(odd_theta_characteristics(g))
  M_even = M[:, even_indices];

  CC = parent(thetas[zeros(Int, 2*g)...])
  prec = precision(CC)
  setprecision(BigFloat, prec)
  #M_even_float = Complex{BigFloat}.(collect(M_even))
  M_even_float = Complex{Float64}.(collect(M_even));
  M_even_float = (x-> abs(x) < 10^(-50) ? zero(ComplexF64) : x).(M_even_float);
  K = permutedims(nullspace(transpose(M_even_float)));
  M_float = Complex{Float64}.(collect(M));
  O = K*(M_float[:,odd_indices])
  rank(O)
end




