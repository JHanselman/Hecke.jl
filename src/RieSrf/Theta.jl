################################################################################
#
#          RieSrf/Theta.jl : Functions for computing theta functions
#
# (C) 2022 Jeroen Hanselman
#
################################################################################


export lll, theta, cholesky_decomposition, siegel_reduction

################################################################################
#
#  Types
#
################################################################################

function theta(z::Array{acb}, RS::RiemannSurface; char::Tuple{Vector{S}, Vector{S}} = (zeros(Int, genus(RS)), zeroes(Int, genus(RS))), derivs::Array{acb}=[], derivs_t::Array{Tuple{S, S}}=[]) where S<:IntegerUnion
    
  tau = small_period_matrix(RS)
  
  tau, U = siegel_reduction(tau)
  
  #tau = X + i*Y
  X = real(tau)
  Y = imag(tau)
  
  #Find T upper-triangular with transpose(T)*T = Y
  T = transpose(cholesky_decomposition(Y))
  g = genus(RS)
  
  if length(z)!= g
    error("z needs to be an element of C^g")
  end
  
  
  C = AcbField(precision(z))
  Rc = ArbField(precision(z))
  pi = const_pi(Rc)
  i = onei(C)
  
  eps = Rc(10^(-30)) #Should depend on precision

  rho = norm(shortest_vectors(T)[1]*sqrt(pi))
  
  N = 1
  
  R0 = (sqrt(g + 2*N + sqrt(g^2 + 8*N)) + rho)//2
  
  T_inv_norm = norm(inv(T))
  
  #We compute the radius of the ellipsoid over which we take the sum needed to bound the error in the sum by eps (See Theorem 3.1 in Agostini, Chua) 
  R_function = function(x::arb, eps::arb)
    Rc = parent(x)
    return (2*pi)^N * g//2 * (2//rho)^g * sum([binomial(N, j) * T_inv_norm^j * sqrt(g)^(N - j) * gamma(Rc((g + j)//2), (x - rho//2)^2) for j in (0:N)]; init = zero(Rc)) - eps
  end
  
  #We want to find the max(R0, x) where x is the solution to R_function(x, eps) = 0
  #Taking x bigger will only improve the error bound, but we want x to be as small as possible
  #to speed up later computations. We therefore look for an x for which R_function(x, eps) is small 
  #and negative.
  #As R_function is monotonic descending we first determine an R1 for which R_function(R1, eps) <0
  #and then subdivide intervals until we find a solution that satisfies our requirements
  
  R1 = R0
  err = Rc(10^(-20))
  
  #Find an R1 such that R_function becomes negative
  while(R_function(R1, eps) > 0)
    R1 = R1 + R0
  end
  
  if R1 != R0
    while 0 < R_function(R0, eps) || R_function(R0, eps) < -err 
      Rmid = (R0 + R1)/2
      middle = R_function(Rmid, eps)
      if middle < 0 
        R1 = Rmid
      else
        R0 = Rmid
      end
    end
  end
  
  radius_ellipsoid = R1
  
  
  
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
  g = nrows(tau)
  
  Rc = base_ring(real(tau))
  Cc = base_ring(tau)
  
  Aq = [zero_matrix(Rc, 1, 1) zero_matrix(Rc, 1, g-1);zero_matrix(Rc, g-1, 1) identity_matrix(Rc, g-1)]
  Bq = [-identity_matrix(Rc, 1) zero_matrix(Rc, 1, g-1);zero_matrix(Rc, g-1, 1) zero_matrix(Rc, g-1, g-1)]
  Cq = -Bq
  Dq = Aq
  
  quasi_inversion = [Aq Bq; Cq Dq]
  
  Gamma = identity_matrix(Rc, 2*g)
  e = zero(Rc)
  
  while e < 1
    Y = imag(tau)
    Y = (Y + transpose(Y)) // Rc(2) #ensure matrix remains symmetric
    
    T = cholesky_decomposition(imag(tau))

    T, U = lll_with_transform(T)
    
    
    Tt = transpose(T)
    
    
    short = 1
    for i in (1 : g)
      if norm(Tt[:, short]) > norm(Tt[:, i])
        short = i
      end
    end
    
    if short!= 1
      S = swap_cols(identity_matrix(Rc, g), 1, i)
      T = S * T
      U = S * U
    end
    
    Tt = transpose(T)
    Y = T*Tt
  
    Gamma = [U zero_matrix(Rc, g, g); zero_matrix(Rc, g, g) inv(transpose(U))] * Gamma;
    tau = U * real(tau) * transpose(U) + onei(Cc) * Y
  
    B = change_base_ring(Rc, map(t -> round(fmpz, t), real(tau)))
    tau -=  change_base_ring(Cc, B)
    Gamma = [identity_matrix(Rc, g) (-B); zero_matrix(Rc, g, g) identity_matrix(Rc, g)]*Gamma 
    e = abs(tau[1,1])
    if e > 1
      return tau, Gamma
    else
      Gamma = quasi_inversion * Gamma
      tau = (Aq * tau + Bq) * inv(Cq * tau + Dq)
    end
  end
end

*(x::acb, y::arb_mat) = x * acb_mat(y)
*(x::arb_mat, y::acb) = y * x
*(x::arb_mat, y::acb_mat) = acb_mat(x) * y
*(x::acb_mat, y::arb_mat) = x * acb_mat(y)
+(x::arb_mat, y::acb_mat) = acb_mat(x) + y
+(x::acb_mat, y::arb_mat) = y + x
-(x::arb_mat, y::acb_mat) = x + (-y)
-(x::acb_mat, y::arb_mat) = x + (-y)
//(x::arb_mat, y::arb) = map(t -> t//y, x)



function acb_mat(A::arb_mat)
  p = precision(base_ring(A))
  Cc = AcbField(p)
  return change_base_ring(Cc, A)
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

function lll(M::arb_mat; ctx = lll_ctx(0.99, 0.51))
  return lll_with_transform(M::arb_mat; ctx = lll_ctx(0.99, 0.51))[1]
end

function lll_with_transform(M::arb_mat; ctx = lll_ctx(0.99, 0.51))
  R = base_ring(M)
  
  #Find number of bits of precision of coefficients of M and subtract 4 to divide by 16 and ensure the numbers are small enough to round
  p = -(ceil(Int,log(maximum(radius, M))/log(2))+4)
  n = nrows(M)
  d = zero_matrix(FlintZZ, n, n)
  round_scale!(d, M, p)
  d, T = lll_with_transform(d, ctx)
  T = change_base_ring(R, T)
  return T*M, T
end

function lll_gram_with_transform(M::arb_mat; ctx = lll_ctx(0.99, 0.51))
  R = base_ring(M)
  
  #Find number of bits of precision of coefficients of M and subtract 4 to divide by 16 and ensure the numbers are small enough to round
  p = -(ceil(Int,log(maximum(radius, M))/log(2))+4)
  n = nrows(M)
  d = zero_matrix(FlintZZ, n, n)
  round_scale!(d, M, p)
  d, T = lll_gram_with_transform(d, ctx)
  T = change_base_ring(R, T)
  return T*M, T
end

function shortest_vectors(M::arb_mat)
  R = base_ring(M)
  p = -(ceil(Int,log(maximum(radius, M))/log(2))+4)
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

