
function _form_from_entries(R, c)
  x = gens(R)
  half = inv(base_ring(R)(2))
  p = zero(R)
  for (k, (i, j)) in enumerate(_lower(length(x)))
    p += (i == j ? c[k] * half : c[k]) * x[i] * x[j]
  end
  return p
end

homogeneous_monomial_exponents(n, d) = n == 1 ? [[d]] : [[k; e] for k in d:-1:0 for e in _exps(n - 1, d - k)]
_coeffs(p, es) = [coeff(p, e) for e in es]
slot = Dict((i, j) => k for (k, (i, j)) in enumerate(lower(g-1)))
half = inv(CC(2))

#Reconstruction as usual
Qxy, (x, y) = polynomial_ring(QQ, [:x, :y])
f =  2*x^5*y^3 + 5*x^4*y^3 - 9*x^4*y^2 + 3*x^3*y - 4*x^2*y^2 - 3*x*y^3 + 1

prec = 500
RS = riemann_surface(f, prec; superelliptic = false, model = :original)
g = genus(RS)
tau = small_period_matrix(RS)
CC = base_ring(tau)
thetas = Hecke.thetas([zero(CC) for _ in 1:5], tau)
thetas_prym = prym_thetas(5, thetas)

sign_data = nothing
pairs_prym = _loaded_sign_data(sign_data, g - 1)

correct_signs_with_data!(thetas_prym, g - 1, pairs_prym)
K, q_K = odd_theta_gradient_kernel(g, thetas)
K_prym, q_K_prym = odd_theta_gradient_kernel(g - 1, thetas_prym)

lower(n) = [(i, j) for j in 1:n for i in j:n]
pairs = lift_prym_indices(g)
n = length(pairs)
HiHis = zero_matrix(CC, n, length(lower(g)))
li_sqs = zero_matrix(CC, n, length(lower(g - 1)))
for (d, (i1, i2)) in enumerate(pairs)
  for (k, (a, b)) in enumerate(lower(g))
    HiHis[d, k] = K[i1, a] * K[i2, b] + K[i2, a] * K[i1, b]
  end
  for (k, (a, b)) in enumerate(lower(g - 1))
    li_sqs[d, k] = K_prym[d, a] * K_prym[d, b]
  end
end

O = RSR._numerical_kernel_data(transpose(li_sqs); nullity = n - length(lower(g - 1)))
M_basis = O.pivot_columns

TT = transpose(O.kernel) * HiHis
N2, rank_TT, _ = RSR.numerical_kernel(TT)
kernel_quadrics = RSR.numerical_kernel(transpose(N2); nullity = 3)[1]  

#Transformation that maps the pivots to the 10 monomials.
Ab = transpose(li_sqs[M_basis, :])
Alpha = solve(Ab, identity_matrix(CC, 10); side = :right)

#Transform the HiHis accordingly
Mu = transpose(HiHis[M_basis, :]) * Alpha    

#The quadrics as polynomials
R, _ = polynomial_ring(CC, 5; cached = false)
all_quadrics = [_form_from_entries(R, [Mu[s, k] for s in 1:15]) for k in 1:10]

#Matrix consisting of quadrics corresponding to xixj
M = [i == j ? all_quadrics[slot[(i, i)]] : half * all_quadrics[slot[(max(i, j), min(i, j))]] for i in 1:4, j in 1:4]
R = parent(M[1, 1])
x = gens(R)
e3 = homogeneous_monomial_exponents(5, 3)
e4 = homogeneous_monomial_exponents(5, 4)

#The quadrics in the kernel written as polynomials
quadric_pols = [_form_from_entries(R, [kernel_quadrics[s, t] for s in 1:15]) for t in 1:3]

#Quartics that are multiples of the quadrics
scroll4 = [x[a] * x[b] * q for q in quadric_pols for a in 1:5 for b in a:5]
S4q = matrix(CC, 45, 70, reduce(vcat, [_coeffs(p, e4) for p in scroll4]))
_, dim_I4S, _ = RSR.numerical_kernel(S4q)

#Quartics coming from minors using all of the quadrics
minors = [M[i, k] * M[j, l] - M[i, l] * M[j, k] for i in 1:4 for j in i+1:4 for k in 1:4 for l in k+1:4]
allq = [scroll4; minors]
S4 = matrix(CC, length(allq), 70, reduce(vcat, [_coeffs(p, e4) for p in allq]))
Z4, dim_I4X, _ = RSR.numerical_kernel(S4)


#Use the extra quadrics to produce new cubics

#Cubics simply coming from muliplying by a linear factor
scroll3 = [x[a] * q for q in quadric_pols for a in 1:5]
S3 = matrix(CC, 15, 35, reduce(vcat, [_coeffs(p, e3) for p in scroll3]))
Z3, dim_I3S, _ = RSR.numerical_kernel(S3)

# cubic in I_3(X) if and only if x_m * cubic is annihilated by the kernel Z4 of S4 for all m
idx4 = Dict(e => k for (k, e) in enumerate(e4))
nz = ncols(Z4)
L = zero_matrix(CC, 5 * nz, 35)
for m in 1:5, (s, e) in enumerate(e3)
  em = copy(e); em[m] += 1
  r4 = idx4[em]
  for t in 1:nz
    L[(m - 1) * nz + t, s] = Z4[r4, t]
  end
end
C3, rL, _ = RSR.numerical_kernel(L)

dim_I3X = ncols(C3)
cubic(col) = sum(C3[s, col] * prod(x .^ e3[s]) for s in 1:35)

#Get new cubics
P = transpose(Z3) * C3
kdP = RSR._numerical_kernel_data(P)
new_cubics = [cubic(c) for c in kdP.pivot_columns]




