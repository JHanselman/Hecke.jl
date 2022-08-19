################################################################################
#
#          RieSrf/RiemannSurface.jl : Riemann surfaces
#
# (C) 2022 Jeroen Hanselman
#
################################################################################

export RieSrf, CPath

export RiemannSurface, discriminant_points, embedding, genus, precision, fundamental_group_of_punctured_P1, c_line, max_radius, radius_factor, find_paths_to_end, start_point, end_point, c_arc, sheet_ordering, embed_mpoly, path_type, analytic_continuation, reverse, assign_permutation, permutation, monodromy_representation, monodromy_group, minimal_spanning_tree

################################################################################
#
#  Types
#
################################################################################

mutable struct CPath

  path_type::Int
  start_point::acb
  end_point::acb
  C::AcbField
  
  center::acb
  radius::arb
  
  length::arb
  gamma::Any
  orientation::Int
  permutation::Perm{Int}
  
  #Path type index:
  #0 is a line
  #1 is an arc
  #2 is a circle
  
  function CPath(a::acb, b::acb, path_type::Int, c::acb = zero(parent(a)), radius::arb = real(zero(parent(a))), orientation::Int = 1)
  
    P = new()
    P.C = parent(a)
    P.start_point = a
    P.end_point = b
    P.path_type = path_type
    P.center = c
    P.radius = radius
    P.orientation = orientation
    
    #Line
    if path_type == 0
      gamma = function(t::arb)
        return (a + b)//2 + (b - a)//2 * t
      end
      length = abs(b - a)
    end
    
    Cc = P.C
    
    i = onei(Cc)
    piC = real(const_pi(Cc))
    
    #Round real or imag part to zero to compute angle if necessary
    prec = precision(Cc)
    zero_sens = floor(prec*log(2)/log(10)) - 5
    
    a_diff = a - c
    
    if abs(real(a_diff)) < 10^(-zero_sens)
      a_diff = Cc(imag(a_diff))*i
    end
    
    if abs(imag(a_diff)) < 10^(-zero_sens)
      a_diff = Cc(real(a_diff))
    end
    
    b_diff = b - c
    
    if abs(real(b_diff)) < 10^(-zero_sens)
      b_diff = Cc(imag(b_diff))*i
    end
    
    if abs(imag(b_diff)) < 10^(-zero_sens)
      b_diff = Cc(real(b_diff))
    end
    
    phi_a = mod2pi(angle(a_diff))
    phi_b = mod2pi(angle(b_diff))
    
    if orientation == 1
      if phi_b < phi_a
        phi_b += 2*piC
      end
    elseif orientation == - 1
       if phi_a < phi_b
        phi_a += 2*piC
      end
    end
    
    
    
    #Arc
    if path_type == 1
      gamma = function(t::arb)
        return c + radius * exp(i * ((phi_a + phi_b)//2 + (phi_b - phi_a)//2 * orientation * t))
      end
      
      length = abs((phi_b - phi_a)) * radius
      
    end
    
    #Full circle
    if path_type == 2
      gamma = function(t::arb)
        #Minus radius as gamma(-1) = a
        return c - radius * exp(i * (phi_a + piC * t ))
      end
      length = 2 * piC * radius
    end
    
    P.gamma = gamma
    P.length = length
    return P
  end

end

mutable struct RiemannSurface
  defining_polynomial::MPolyElem
  genus::Int
  tau::acb_mat
  prec::Int
  embedding::Union{PosInf, InfPlc}
  discriminant_points::Vector{acb}
  closed_chains::Vector{CPath}

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

function reverse(G::CPath)
  
  p_type = path_type(G)
  
  if p_type == 0
    G_rev = c_line(end_point(G), start_point(G))
  else #Circle or arc
    G_rev = c_arc(end_point(G), start_point(G), center(G), orientation = -orientation(G))
  end
  assign_permutation(G_rev, inv(permutation(G)))
  return G_rev
end

function c_line(start_point::acb, end_point::acb)
  return CPath(start_point, end_point, 0)
end

function c_arc(start_point::acb, end_point::acb, center::acb; orientation::Int = 1)
  if contains(end_point, start_point) && contains(start_point, end_point)
    return CPath(start_point, start_point, 2, center, abs(start_point - center), orientation)
  else
    return CPath(start_point, end_point, 1, center, abs(start_point - center), orientation)
  end
end

function show(io::IO, gamma::CPath)
  p_type = path_type(gamma)
  if p_type< 0 || p_type > 2
    error("Path type does not exist")
  end
  
  x0 = start_point(gamma)
  x1 = end_point(gamma)
  if p_type == 0
    print(io, "Line from $(x0) to $(x1).")
  else
    r = radius(gamma)
    c = center(gamma)
    if p_type == 1
      print(io, "Arc around $(c) with radius $(r) starting at $(x0) and ending at $(x1).")
    elseif p_type == 2
      print(io, "Circle around $(c) with radius $(r) starting at $(x0).")
    end
  end
  end

function path_type(G::CPath)
  return G.path_type
end

function start_point(G::CPath)
  return G.start_point
end

function end_point(G::CPath)
  return G.end_point
end

function center(G::CPath)
  if 1 <= path_type(G) <= 2
    return G.center
  else
    error("Path is not a circe or an arc")
  end
end

function radius(G::CPath)
  if 1 <= path_type(G) <= 2
    return G.radius
  else
    error("Path is not a circe or an arc")
  end
end

function evaluate(G::CPath, t::arb)
  return G.gamma(t)
end

function length(G::CPath)
  return G.length
end

function orientation(G::CPath)
  return G.orientation
end

function assign_permutation(G::CPath, permutation::Perm{Int})
  G.permutation = permutation
end

function permutation(G::CPath)
  return G.permutation
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
  return ArbField(precision(RS))(1//4)
end

function radius_factor(RS::RiemannSurface)
  return ArbField(precision(RS))(2//5)
end

function monodromy_representation(RS::RiemannSurface)
  paths, pi1_gens = fundamental_group_of_punctured_P1(RS, true)
  f = defining_polynomial(RS)
  m = degree(f, 2)
  
  s_m = SymmetricGroup(m)
  
  for i in (1:length(paths))
    path = paths[i]
    N = ceil(Int, length(path)) +1
    if path_type(path) in [1,2]
      N *= 4
    end
      
      
    Rc = ArbField(precision(RS))
     
    abscissae = [Rc(n//N) for n in (-N + 1: N - 1)] 
     
    An = analytic_continuation(RS, path, abscissae)
    
    path_perm = sortperm(An[end][2], lt = sheet_ordering)
    assign_permutation(path, inv(s_m(path_perm)))
  end
  
  mon_rep = []
  
  for gamma in pi1_gens
    chain = map(t -> ((t > 0) ? paths[t] : reverse(paths[-t])), gamma)
    gamma_perm = prod(map(permutation, chain))
    
    if gamma_perm != one(s_m)
      push!(mon_rep, (chain, gamma_perm))
     end
  end
  
  return mon_rep
  
end

function monodromy_group(RS::RiemannSurface)
  mon_rep = monodromy_representation(RS)
  gens = map(t -> t[2], mon_rep)
  return closure(gens, *)
end

#Follows algorithm 4.3.1 in Neurohr
function fundamental_group_of_punctured_P1(RS::RiemannSurface, abel_jacobi::Bool = true)
  
  #Compute the exceptional values x_i
  D_points = discriminant_points(RS)
  d = length(D_points)
  Cc = parent(D_points[1])
  Rc = ArbField(precision(RS))
  
  #Step 1 compute a minimal spanning tree
  edges = minimal_spanning_tree(D_points)
  
  #Choose a suitable base point and connect it to the spanning tree

  #Multiple ways to choose the base point. 
  #This one is most suitable when computing abel-jacobi maps. 
  #Take some integer point to the left of the point with the smallest real part
    
  
  if abel_jacobi
    
    #Real part should already be minimal in D_points
    x0 = Cc(min(floor(fmpz, real(D_points[1]) - 2*max_radius(RS)), -1))
    
    
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
    push!(D_points, x0)
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

  path_edges = []
  past_nodes = [d + 1]
  current_node = d + 1
  
  left_edges = filter(t -> t[1] == current_node && !(t[2] in past_nodes), edges)
  right_edges = filter(t -> t[1] == current_node && !(t[2] in past_nodes), map(reverse,edges))
  
  leftright = vcat(left_edges, right_edges)
  
  current_angle = zero(Rc)
  
  angle_ordering = function(t1::Tuple{Int, Int}, t2::Tuple{Int, Int})
    return mod2pi(angle(D_points[t1[2]] - D_points[t1[1]]) - current_angle) < mod2pi(angle(D_points[t2[2]] - D_points[t2[1]]) - current_angle)
  end
      
  sort!(leftright, lt = angle_ordering)
  
  path_edges = vcat(path_edges, leftright)
  current_level = vcat(left_edges, right_edges)
  
  while length(path_edges) < length(edges)
    next_level = []
    for edge in current_level
    
      previous_node = edge[1]
      current_node = edge[2]
      current_angle = angle(D_points[previous_node] - D_points[current_node])
      
      left_edges = filter(t -> t[1] == current_node && !(t[2] in past_nodes), edges)
      right_edges = filter(t -> t[1] == current_node && !(t[2] in past_nodes), map(reverse, edges))
      leftright = vcat(left_edges, right_edges)
    
      angle_ordering = function(t1::Tuple{Int, Int}, t2::Tuple{Int, Int})
        return mod2pi(angle(D_points[t1[2]] - D_points[t1[1]]) - current_angle) < mod2pi(angle(D_points[t2[2]] - D_points[t2[1]]) - current_angle)
      end
      
      sort!(leftright, lt = angle_ordering)
      next_level = vcat(next_level, leftright)
      path_edges = vcat(path_edges, leftright)
      
      push!(past_nodes, current_node) 
    end
    
    current_level = next_level
  end
  
  #Construct paths to every end point starting at x0 using a Depth-First Search
  
  #Paths to all nodes
  paths = [[(d+1, d+1)]]
  
  ordered_disc_points = []
  find_paths_to_end([(d+1, d+1)], paths, path_edges, ordered_disc_points)
  ordered_disc_points = map(t -> D_points[t], ordered_disc_points)
  
  radii = [min(max_radius(RS), radius_factor(RS) * minimum(map(t -> abs(t - D_points[j]), vcat(D_points[1:j-1], D_points[j+1:end])))) for j in (1:d)]
  
  c_lines = CPath[]
  
  
  #Find the line pieces of the paths.
  for edge in path_edges
    a = D_points[edge[1]]
    b = D_points[edge[2]]
    ab_length = b - a
    
    #Base point is not a discriminant point, so we don't need to circle around it
    if edge[1] == d + 1
      new_start_point = a
    else
      #Intersect the line between a and b with the circle of radius r_a around a
      new_start_point = a + (radii[edge[1]])*ab_length//(abs(ab_length))
    end
    #Intersect the line between a and b with the circle of radius r_b around b
    new_end_point = b - (radii[edge[2]])*ab_length//(abs(ab_length))
    push!(c_lines, c_line(new_start_point, new_end_point))
  end
  
  paths = map(t -> t[2:end], paths[2:end])
  path_indices = map(path -> map(t -> findfirst(x -> x == t, path_edges), path), paths)

  c_arcs = CPath[]
  paths_with_arcs = []
  
  #We reconstruct the paths 
  for path in reverse(path_indices)
    
    i = path[end]
    loop = []
    
    arc_start = arc_end = end_point(c_lines[i])
    center = D_points[path_edges[i][end]]
    
    #We need to loop around the end of the path, but we may
    #have already constructed parts of the loop when constructing previous paths
    #We therefore find these first and add them.
    
    n = length(c_arcs)
    for j in (1:n)
      arc = c_arcs[j]
      if contains(arc_end, end_point(arc)) && contains(end_point(arc), arc_end)
        push!(loop, j + d)
        arc_end = start_point(arc)
      end
    end
    
    push!(c_arcs, c_arc(arc_start, arc_end, center))
    push!(loop, d + n + 1)

    path_to_loop = []

    #Now we attach the line piece
    push!(path_to_loop, i)
   
    #We add the inverse arcs as moving towards the points we want to encircle we move clockwise 
    for k in (length(path)-1:-1:1)  
    
      arc_buffer = []
      old_line_piece = c_lines[path[k+1]]
      new_line_piece = c_lines[path[k]]
      arc_start = start_point(old_line_piece)
      arc_end = end_point(new_line_piece)
      center = D_points[path_edges[path[k]][end]]
   
     #Similar to before. Maybe make a function out of it
      n = length(c_arcs)
      for j in (1:n)
        arc = c_arcs[j]
        if contains(arc_end, end_point(arc)) && contains(end_point(arc), arc_end)
          push!(arc_buffer, -j - d)
          arc_end = start_point(arc)
        end
      end
     
      if arc_start != arc_end
        push!(c_arcs, c_arc(arc_start, arc_end, center))
        push!(arc_buffer, - d - n - 1)
      end
     
      path_to_loop = vcat(path_to_loop, reverse(arc_buffer))
      push!(path_to_loop, path[k])
    end
    push!(paths_with_arcs, vcat(reverse(path_to_loop), reverse(loop), -path_to_loop))
  end
  return vcat(c_lines, c_arcs), reverse(paths_with_arcs)
end

function analytic_continuation(RS::RiemannSurface, path::CPath, abscissae::Vector{arb})
  v = embedding(RS)
  prec = precision(RS)
  Rc = ArbField(prec)
  
  f = embed_mpoly(defining_polynomial(RS), v, prec)
  
  Cc = base_ring(f)
  
  f = change_base_ring(Cc, f, parent = parent(f))

  m = degree(f, 2)
  
  u = vcat([-one(Rc)], abscissae, [one(Rc)])
  N = length(u)
  
  x_vals = zeros(Cc, N)
  y_vals = [zeros(Cc, m) for i in (1:N)]
  z = zeros(Cc, m)
  x_vals[1] = evaluate(path, u[1])
  
  Kxy = parent(f)
  Ky, y = PolynomialRing(base_ring(Kxy), "y")
  
  
  y_vals[1] = sort!(roots(f(x_vals[1], y), initial_prec = prec), lt = sheet_ordering)
  for l in (2:N)
    x_vals[l] = evaluate(path, u[l])
    z .= y_vals[l-1]
    y_vals[l] .= recursive_continuation(f, x_vals[l-1], x_vals[l], z)
  end
  return collect(zip(x_vals, y_vals))
end

function recursive_continuation(f, x1, x2, z)
  Kxy = parent(f)
  Ky, y = PolynomialRing(base_ring(Kxy), "y")
  Cc = base_ring(f)
  prec = precision(Cc)
  m = degree(f, 2)
  temp_vec = acb_vec(m)
  temp_vec_res = acb_vec(m)
  d = reduce(min, [abs(z[i] - z[j]) for (i, j) in filter(t-> t[1] != t[2], [a for a in Iterators.product((1:m), (1:m))])]) 
  W = [ f(x2, z[i]) // prod([z[i] - z[j] for j in vcat((1:i - 1), i+1:m)];init = one(Cc)) for i in (1:m)]
  w = reduce(max, map(t -> real(t)^2 +imag(t)^2, W))
  
  if w < d // (2*m)
    fill!(temp_vec, z)
    dd = ccall((:acb_poly_find_roots, libarb), Cint, (Ptr{acb_struct}, Ref{acb_poly}, Ptr{acb_struct}, Int, Int), temp_vec_res, f(x2, y), temp_vec, 0, prec)

    @assert dd == m
    z .= array(Cc, temp_vec_res, m)
    
    acb_vec_clear(temp_vec, m)
    acb_vec_clear(temp_vec_res, m)
    
    return z
  else
    midpoint = (x1 + x2)//2
    return recursive_continuation(f, midpoint, x2, recursive_continuation(f, x1, midpoint, z))
  end
  
end

function find_paths_to_end(path, paths, edges, ordered_disc_points)
  end_path = path[end][2]
  temp_paths = paths
  for (start_edge, end_edge) in edges
    if start_edge == end_path
      push!(ordered_disc_points, end_edge)
      newpath = vcat(path, [(start_edge, end_edge)])
      push!(paths, newpath)
      find_paths_to_end(newpath, paths, edges, ordered_disc_points)
    end
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
  
  disjoint_trees = [Set([i]) for i in (1:N)]
  
  i = 1
  
  while length(tree) < N - 1
  
    (s1, s2) = edge_weights[i][2]
    
    s1_index = findfirst(t -> s1 in t, disjoint_trees)
    
    s1_tree = disjoint_trees[s1_index]
    
    if s2 in s1_tree
      #continue
    else
      s2_tree = popat!(disjoint_trees, findfirst(t -> s2 in t, disjoint_trees))
      push!(tree, (s1, s2))
      union!(s1_tree, s2_tree) 
    end
    i+= 1
  end
  
  return tree
end

function assure_has_discriminant_points(RS::RiemannSurface)
  if isdefined(RS, :discriminant_points)
    return nothing
  else
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
    RS.discriminant_points = D_points
    return nothing
  end
end

function discriminant_points(RS::RiemannSurface, copy::Bool = true)
  assure_has_discriminant_points(RS)
  if copy
    return deepcopy(RS.discriminant_points)
  else
    return RS.discriminant_points
  end
end

function embed_poly(f::PolyElem{nf_elem}, v::T, prec::Int = 100) where T<:Union{PosInf, InfPlc}
  coeffs = coefficients(f)
  coeffs = map(t -> evaluate(t, v, prec), coeffs)
  
  Cx, x = PolynomialRing(AcbField(prec), "x")
  
  return sum(coeffs[i]*x^(i - 1) for i in (1:length(coeffs)))
end

function embed_mpoly(f::MPolyElem, v::T, prec::Int = 100) where T<:Union{PosInf, InfPlc}
  return map_coefficients(x -> evaluate(x, v, prec), f)
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

