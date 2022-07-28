################################################################################
#
#          RieSrf/NumIntegrate.jl : Numerical integration
#
# (C) 2022 Jeroen Hanselman
#
################################################################################

export gauss_legendre_integration_points, gauss_chebyshev_integration_points, tanh_sinh_quadrature_integration_points

################################################################################
#
#  Gauss-Legendre
#
################################################################################

function gauss_legendre_integration_points(N::T, prec::Int = 100) where T <: IntegerUnion
  
  Rc = ArbField(prec)

  N = Int(N)
  m = floor(Int, (N +1)//2)
  
  ab = zeros(Rc, m)
  w = zeros(Rc, m)
  
  for l in (0:m-1)
    ccall((:arb_hypgeom_legendre_p_ui_root, libarb), Nothing, (Ref{arb}, Ref{arb}, UInt, UInt, Int), ab[l+1], w[l+1], N, l, prec)
  end
  
  if isodd(N)
    abscissae = vcat(-ab, reverse(ab[1:m-1]))
    weights = vcat(w, reverse(w[1:m-1]))
  else
    abscissae = vcat(-ab, reverse(ab))
    weights = vcat(w, reverse(w))
  end
  return abscissae, weights
end

function gauss_chebyshev_integration_points(N::T, prec::Int = 100) where T <: IntegerUnion
  Rc = ArbField(prec)
  pi_N12 = const_pi(Rc)//(2*N)
  
  m = floor(Int, N//2)
  
  ab = zeros(Rc, m)
  w = zeros(Rc, m)
  
  for l in (1:m)
    ab[l] = cos(pi_N12 * (2*l - 1))
  end
  
  isodd(N) ? abscissae = vcat(-ab, [zero(Rc)], reverse(ab)) : abscissae = vcat(-ab, reverse(ab))
  return abscissae, fill(const_pi(Rc)//(N), N)  
end

function tanh_sinh_quadrature_integration_points(N::T, h::arb, lambda::arb = const_pi(parent(h))//2) where T <: IntegerUnion
  Rc = parent(h)
  N = Int(N)

  abscissae = zeros(Rc, N)
  weights = zeros(Rc, N)
  
  lamh = lambda * h
  
  for l in (1:N)
    lh = l*h
    lamsin_lh = lambda*sinh(lh)
    
    abscissae[l] = tanh(lamsin_lh)
    weights[l] = lamh * cosh(lh)//(cosh(lamsin_lh))^2 
  end
  
  abscissae = vcat(-reverse(abscissae), [zero(Rc)], abscissae)
  weights = vcat(reverse(weights), [lamh], weights)
  
  return abscissae, weights
end

