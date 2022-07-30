################################################################################
#
#          RieSrf/RiemannSurface.jl : Riemann surfaces
#
# (C) 2022 Jeroen Hanselman
#
################################################################################

export RieSrf, CPath

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

mutable struct CPath

  path_type::Int
  start_point::acb
  end_point::acb
  
  
  center::acb
  radius::arb
  counterclockwise::Bool
  
  length::arb
  
  #Path type index:
  #0 is a line
  
  function CPath(start_point::acb, end_point::acb, path_type::Int, center::acb = zero(parent(start_point)), radius::arb = zero(parent(start_point)), counterclockwise::Bool = true)
  
    P = new()
    P.start_point = start_point
    P.end_point = end_point
    P.path_type = path_type
    P.center = center
    P.radius = radius
    P.counterclockwise = counterclockwise
    return P
  end

end

function c_line(start_point::acb, end_point::acb)
  return CPath(start_point, end_point, 0)
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

function embedding(RS::RiemannSurface)
  return RS.embedding
end

function small_period_matrix(RS::RiemannSurface)
  return tau
end

function precision(RS::RiemannSurface)
  return RS.prec
end

function max_radius(RS::RiemannSurface)
  return 1//4
end

#Follows algorithm 4.3.1 in Neurohr
function fundamental_group(RS::RiemannSurface, abel_jacobi::Bool = false)
  
  #Compute the exceptional values x_i
  D_points = discriminant_points(RS)
  d = length(D_points)
  Cc = parent(D_points[1])
  
  #Step 1 compute a minimal spanning tree
  edges = minimal_spanning_tree(D_points)
  
  #Choose a suitable base point and connect it to the spanning tree

  #Multiple ways to choose the base point. 
  #This one is most suitable when computing abel-jacobi maps. 
  #Take some integer point to the left of the point with the smallest real part
    
  
  if abel_jacobi
    
    #Real part should already be minimal in D_points
    x0 = Cc(min(floor(fmpz, real(D_points[1]) - 2*max_radius(RS)), -1))
    push!(D_points, x0)
    
    #Connect base point to closest point in D_points
    closest = 1
    distance = abs(x0 - D_points[1])
    for i in (2:length(D_points))
      new_distance = abs(x0 - D_points[i])
      if distance > new_distance
        closest = i
        distance = new_distance
      end
    end
    
    push!(edges, (d +1, closest))
  else
  #Here we take the one that is most suitable if one doesn't need to compute Abel-Jacobi maps according to Neurohr, i.e. we split the longest edge in the middle. 
  #(Last edge should be the longest in the way we compute minimal_spanning trees right now.)
    
    left = edges[end][1]
    right = edges[end][2]
    pop!(edges)
    x0 = (D_points[left] + D_points[right])//2
    push!(D_points, x0)
    push!(edges, (d + 1, left))
    push!(edges, (d + 1, right))
  end
  
  #Now we sort the points by angle and level

  paths = CPath[]
  past_nodes = [d + 1]
  current_node = d + 1
  
  left_edges = filter(t -> t[1] == current_node && !(t[2] in past_nodes), edges)
  right_edges = filter(t -> t[1] == current_node && !(t[2] in past_nodes), map(reverse,edges))
  
  leftright = vcat(left_edges, right_edges)
    
  angle_ordering = function(t1::Tuple{Int, Int}, t2::Tuple{Int, Int})
    return mod2pi(angle(current_node - D_points[t1[2]]) - current_angle) < mod2pi(angle(current_node - D_points[t2[2]]) - current_angle)
  end
      
  sort!(leftright, lt = angle_ordering)
  
  paths = vcat(paths, leftright)
  current_level = vcat(left_edges, right_edges)
  
  while length(paths) < length(edges)
    next_level = []
    for edge in current_level
    
      previous_node = edge[1]
      current_node = edge[2]
      current_angle = angle(D_points[previous_node] - D_points[current_node])
      
      left_edges = filter(t -> t[1] == current_node && !(t[2] in past_nodes), edges)
      right_edges = filter(t -> t[1] == current_node && !(t[2] in past_nodes), map(reverse, edges))
      leftright = vcat(left_edges, right_edges)
    
      angle_ordering = function(t1::Tuple{Int, Int}, t2::Tuple{Int, Int})
        return mod2pi(angle(current_node - D_points[t1[2]]) - current_angle) < mod2pi(angle(current_node - D_points[t2[2]]) - current_angle)
      end
      
      sort!(leftright, lt = angle_ordering)
      next_level = vcat(next_level, leftright)
      paths = vcat(paths, leftright)
      
      push!(past_nodes, current_node) 
    end
    
    current_level = next_level
  end
  
  
end

function Base.mod2pi(x::arb)
  pi2 = 2*const_pi(parent(x))
  while x < 0
    x += pi2
  end
  
  while x > pi2
    x -= pi2
  end
  
  return x
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
  
  tree = Tuple{Int, Int}[]
  
  nodes = Int[]
  
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
  
  D1 = vcat(acb[],[roots(fac, initial_prec = prec) for fac in disc_y_factors]...)
  D2 = vcat(acb[],[roots(fac, initial_prec = prec) for fac in a0_factors]...)
  D_points = sort!(vcat(D1, D2), lt = sheet_ordering)
    @show typeof(D2)
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

