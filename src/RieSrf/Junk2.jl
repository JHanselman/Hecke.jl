
GF2 = GF(2)


thetas_prym_sq = prym_thetas_sq(g, thetas)
O = odd_theta_relations(g-1, thetas_prym_sq)

odds = odd_theta_characteristics(g-1)

odd_prym_indices = char_to_index.(collect.(odd_theta_characteristics(g-1)))
odd_indices = char_to_index.(collect.(odd_theta_characteristics(g)))

rho1 = GF2.([1,0,0,0,0,0,0,0,0,0])
rho2 = GF2.([1,1,0,0,0,0,1,0,0,1])
rho3 = GF2.([0,1,0,1,0,0,1,1,0,0])
rho4 = GF2.([0,1,0,0,1,0,0,0,0,1])
rho5 = GF2.([1,1,1,1,1,1,1,1,1,1])
rho6 = GF2.([1,0,1,1,1,0,1,1,0,1])
rho7 = GF2.([1,0,1,0,1,1,0,1,0,1])
rho8 = GF2.([0,0,1,0,1,1,0,1,0,0])

R = [rho1, rho2, rho3, rho4, rho5, rho6, rho7, rho8]

bigM = Vector{AcbFieldElem}[]

for r in R
  M = construct_fay_matrix(g, thetas, r)
  bigM = [bigM ; M]
end

bigM_float = Complex{Float64}.(collect(matrix(bigM)[:,odd_indices]))
K = nullspace(bigM_float)

I = lift_prym_indices(g)

HiHis = Vector{Complex{Float64}}[]
for i in (1:length(odds)) 
  i1, i2 = I[i]
  L = K[i1,:] * transpose(K[i2, :])
  LL = L + transpose(L)
  HiHi = collect(Iterators.flatten(LL))
end

HiHis2 = mapreduce(permutedims, vcat, HiHis)
TT =  O * HiHis2

(x-> abs(x) < 10^(-12) ? zero(ComplexF64) : x).(TT)
function lift_prym_indices(g::Int)
  odds = odd_theta_characteristics(g-1)
  lifted = odd_theta_characteristics(g)
  result = []
  for char in odds
    delta_new1 = (0, char[1:g-1]..., 0, char[g:2*(g-1)]...)
    delta_new2 = (0, char[1:g-1]..., 1, char[g:2*(g-1)]...)
    i1 = findfirst(x-> x == delta_new1, lifted)
    i2 = findfirst(x -> x == delta_new2, lifted)
    push!(result, (i1,i2))
  end
  result
end


theta_indices_temp = Hecke.theta_characteristics_indices(g)
theta_indices = theta_indices_temp[2:end]
push!(theta_indices, theta_indices_temp[1])
relations = Vector{Tuple{Vector{Int64}, ZZRingElem}}[]
base = []

V = Iterators.product(repeat([[QQ(0),QQ(1//2)]], 2*g-1)...)


#for v in V
  #rho = collect((v..., QQ(0)))
  test, rel = signs_from_relations(g, thetas, rho, sigma)
  if test 
    push!(relations, rel)
  end
end
#even_indices = char_to_index.(even_theta_characteristics(g))
same_sign = Set([])


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
