################################################################################
#
#          RieSrf/Theta.jl : Functions for computing theta functions
#
# (C) 2022 Jeroen Hanselman
#
################################################################################


export lll, theta, cholesky_decomposition

################################################################################
#
#  Types
#
################################################################################

function theta(z::Array{acb}, RS::RiemannSurface; char::Tuple{Vector{S}, Vector{S}} = (zeros(Int, genus(RS)), zeroes(Int, genus(RS))), derivs::Array{acb}=[], derivs_t::Array{Tuple{S, S}}=[]) where S<:IntegerUnion
    
  tau = small_period_matrix(RS)
  
  #tau = X + i*Y
  X = real(tau)
  Y = imag(tau)
  
  #Find T upper-triangular with transpose(T)*T = Y
  T = transpose(cholesky_decomposition(Y))
  g = genus(RS)
    
  C = AcbField(precision(z))
  pi = const_pi(C)
  i = onei(C)
  
  rho = shortest_vectors(T)*sqrt(pi)
  
  N = nderivs
  
  R = (sqrt(g + 2*N + sqrt(g^2 + 8*N)) + rho)//2
  
  T_inv_norm = norm(inv(T))
  
  R_function = function(x::arb, eps::arb)
    R = parent(x)
    return (2*pi)^N * g//2 * (2//rho)^g * sum([binomial(N, j) * T_inv_norm^j * sqrt(g)^(N - j) * gamma(R((g + j)//2), (x - rho//2)^2) for j in (0:N)]; init = zero(R)) - eps
  end
  
  if length(z)!= g
    error("z needs to be an element of C^g")
  end
    
    
  if length(char[1])!= g || length(char[2])!= g
    error("Characteristic needs to be of length g")
  end
    
  for c in char[1]
    if c < 0 || c > 1
      error("Characteristic needs to be an array of ones and zeroes")
    end
    shift_n[1] =  C(c//2)
  end
    
  for c in char[2]
    if c < 0 || c > 1
      error("Characteristic needs to be an array of ones and zeroes")
    end
    shift_x[2] = C(c//2)
  end
    
  # compute derivatives with respect to tau by converting to derivatives with respect to z using the heat equation
  deriv_t_factor = one(C) # multiply result by this factor
    
  for d in derivs_t
    if d[1] == d[2]
      deriv_t_factor *= //(4*pi*onei)
    else
      deriv_t_factor *= 1//(2*pi*onei)
    end
    deriv = [zeros(C, g), zeros(C, g)]
    deriv[1][d[1]] = one(C)
    deriv[2][d[2]] = one(C)
    derivs = vcat(derivs, deriv)
  end
  # compute theta function
  x = real(z) + shift_x # shift z by characteristic
  y = imag(z)
    
  y0 = inv(tau_im)*y
  exp_part = exp((π*transpose(y)*y0)[1]) # exponential part of theta function
  osc_part = oscillatory_part(tau, x, y0, shift_n, derivs) # oscillatory part of theta function
  return deriv_t_factor*exp_part*osc_part
end


"""
    oscillatory_part(R, x, y0, shift_n, derivs=[])
Compute the oscillatory part of the Riemann theta function. Helper function to [`theta`](@ref).
"""
function oscillatory_part(R::acb_mat, x::Array{<:Real}, y0::Array{<:Real}, shift_n::Array{<:Real}, derivs::Array{}=[])
    nderivs = size(derivs)[1];
    E = [n + shift_n for n in R.ellipsoid[nderivs + 1]]; # shift points in ellipsoid for computing theta function with characteristics
    w = round.(y0);
    w0 = y0 - w;
    s = (2*π*im)^(nderivs) * sum([ (nderivs > 0 ? prod(transpose(d)*(p-w) for d in derivs) : 1) * exp(2*π*im*((0.5*(transpose(p-w)*R.X*(p-w))[1] + transpose(p-w)*x)[1]) - π*(transpose(p+w0)*R.Y*(p+w0))[1]) for p in E]); # compute sum over points in ellipsoid
    return s;
end

function siegel_reduction(tau::acb_mat)
  X = real(tau)
  Y = imag(tau)
  T = cholesky_decomposition(Y)
  
  
end

function real(tau::acb_mat)
  return map(real, tau)
end

function imag(tau::acb_mat)
  return map(imag, tau)
end

function cholesky_decomposition(x::arb_mat)
  z = similar(x, nrows(x), ncols(x))
  p = precision(base_ring(x))
  fl = ccall((:arb_mat_cho, Hecke.libarb), Cint, (Ref{arb_mat}, Ref{arb_mat}, Int), z, x, p)
  @assert fl != 0
  return z
end

function lll(M::arb_mat; ctx = lll_ctx(0.99, 0.51, :gram))
  R = base_ring(M)
  p = precision(R)
  n = nrows(M)
  d = zero_matrix(FlintZZ, n, n)
  round_scale!(d, M, p)
  d, T = lll_with_transform(d, ctx)
  T = change_base_ring(R, T)
  return T*M
end

function shortest_vectors(M::arb_mat)
  R = base_ring(M)
  p = precision(R)
  n = nrows(M)
  d = zero_matrix(FlintZZ, n, n)
  round_scale!(d, M, p)
  L = Zlattice(d)
  U = shortest_vectors(L)
  return [change_base_ring(R, u)*M for u in U]
end

function norm(v::arb_mat)
  return sqrt(sum([a^2 for a in v]))
end

#M = matrix(ArbField(100), 4, 4, [0.7563, 0.4850, 0.4806, 0.3846, 0.4850, 1.3631, 0.2669, -0.3084, 0.4806, 0.2669, 0.7784, -0.4523, 0.3846, -0.3084, -0.4523, 1.7538])

