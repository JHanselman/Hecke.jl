################################################################################
#
#          RieSrf/RiemannSurface.jl : Riemann surfaces
#
# (C) 2022 Jeroen Hanselman
#
################################################################################

export RieSrf

export RiemannSurface, discriminant_points, embedding, genus, precision

################################################################################
#
#  Types
#
################################################################################

mutable struct RiemannSurface
  defining_polynomial::MPolyElem
  genus::Int
  tau::acb_mat
  prec::Int
  embedding::Union{PosInf, InfPlc}
  

  function RiemannSurface(tau::acb_mat)
    RS = new()
    g = ncols(tau)
    if nrows(tau) != g
      error("Matrix needs to be a square matrix")
    end
    RS.genus = g
    prec = precision(parent(M[1,1]))
    RS.small_period_matrix = tau
  end

  function RiemannSurface(f::MPolyElem, v::T, prec = 100) where T<:Union{PosInf, InfPlc}
    K = base_ring(f)
    
    RS = new()
    RS.defining_polynomial = f
    RS.prec = prec
    RS.embedding = v
    
    return RS
  end

end

function defining_polynomial(RS::RiemannSurface)
  return RS.defining_polynomial
end


function defining_polynomial_univariate(RS::RiemannSurface)
  f = defining_polynomial(RS)
  K = base_ring(f)
  Kx, x = PolynomialRing(K, "x")
  Kxy, y = PolynomialRing(Kx, "y")
  
  return f(x, y)
end

function genus(RS::RiemannSurface)
  return RS.genus
end

function embedding(RS)
  return RS.embedding
end

function small_period_matrix(RS)
  return tau
end

function precision(RS)
  return RS.prec
end

function fundamental_group(RS::RiemannSurface)
  D_points = discriminant_points(RS)
  
  x0 = D_points[1]
  
  minimal_spanning_tree(D_points)
  
end


#Could be optimized probably. Kruskal's algorithm
function minimal_spanning_tree(v::Vector{acb})

  edge_weights = []
  
  N = length(v)
  
  #Compute the weights for all the edges
  for i in (1:N)
    for j in (i+1: N)
      push!(edge_weights, (abs(v[i] - v[j]), (i, j)))
    end
  end
  
  sort!(edge_weights) 
  
  tree = []
  
  nodes = []
  
  i = 1
  
  while length(nodes) < N
  
    (s1, s2) = edge_weights[i][2]
    
    if !(s1 in nodes && s2 in nodes)
      push!(tree, (s1, s2))
      union!(nodes, [s1,s2])
    end
    i+= 1
  end
  
  return tree
end

function discriminant_points(RS::RiemannSurface)
  f = defining_polynomial_univariate(RS)
  Kxy = parent(f)
  Kx = base_ring(f)
  
  v = embedding(RS)
  prec = precision(RS)
  
  disc_y_factors = acb_poly[]
  a0_factors = acb_poly[]
  
  for (f,e) in factor(discriminant(f))
    push!(disc_y_factors, embed_poly(f, v, prec))
  end
  
    for (f,e) in factor(leading_coefficient(f))
    push!(a0_factors, embed_poly(f, v, prec))
  end
  
  D1 = vcat([roots(fac, initial_prec = prec) for fac in disc_y_factors]...)
  D2 = vcat([roots(fac, initial_prec = prec) for fac in a0_factors]...)
  D_points = sort!(vcat(D1, D2), lt = sheet_ordering)
  return D_points
end

function embed_poly(f::PolyElem{nf_elem}, v::T, prec::Int = 100) where T<:Union{PosInf, InfPlc}
  coeffs = coefficients(f)
  coeffs = map(t -> evaluate(t, v, prec), coeffs)
  
  Cx, x = PolynomialRing(AcbField(prec), "x")
  
  return sum(coeffs[i]*x^(i - 1) for i in (1:length(coeffs)))
end

#Might need to be made more rigorous due to dealing with arb balls
function sheet_ordering(z1::acb,z2::acb)
  if real(z1) < real(z2) 
    return true
  elseif real(z1) > real(z2) 
    return false
  elseif imag(z1) < imag(z2)
    return true
  elseif imag(z2) < imag(z1)
    return false
  end
end

