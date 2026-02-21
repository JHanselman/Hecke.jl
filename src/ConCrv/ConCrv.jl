################################################################################
#
#          ConCrv/ConCrv.jl : Conics over general fields
#
# (C) 2025 Jeroen Hanselman
#
################################################################################

################################################################################
#
#  Types
#
################################################################################

mutable struct ConCrv{T}
  base_field::Ring
  coeffs::Tuple{T, T, T, T, T, T}
  disc::T

  function ConCrv{T}(coeffs::Vector{T},check::Bool = true) where {T}
    K = parent(coeffs[1])
    
    if length(coeffs) == 3
      append!(coeffs, [zero(K), zero(K), zero(K)])
    elseif length(coeffs) !=6
      error("Length of coefficient array must be either 3 or 6")
    end
    a11, a22, a33, a12, a23, a13 = coeffs
    d = 4*a11 * a22 * a33 - a11 * a23^2 - a12^2 * a33 + a12 * a13 * a23 - a13^2 * a22
    if d != 0 && check
      C = new{T}()
      C.coeffs = Tuple(coeffs)
      C.base_field = K
      C.disc = d
    else
      error("Discriminant is zero")
    end
    return C
  end
end

mutable struct ConCrvPt{T}
  coordx::T
  coordy::T
  coordz::T
  parent::ConCrv{T}

  function ConCrvPt{T}(C::ConCrv{T}, coords::Vector{T}, check::Bool = true) where {T}
    K = base_field(C)
    P = new{T}()
    if check
      if !is_on_curve(C, coords)
        error("Point is not on the curve")
      end
    end

    P.parent = C
    if coords[3] == 0
      P.coordx = coords[1]
      P.coordy = coords[2]
      P.coordz = coords[3]
    else
      #Don't have numerators, denominators and gcd over finite fields
      if T <: FinFieldElem
        scalar = inv(coords[3])
        P.coordx = coords[1]*scalar
        P.coordy = coords[2]*scalar
        P.coordz = coords[3]*scalar
      else

        #Eliminate denominators
        x = numerator(coords[1]) * denominator(coords[3]) * denominator(coords[2])
        y = numerator(coords[2]) * (denominator(coords[3]) * denominator(coords[1]))
        z = numerator(coords[3]) * denominator(coords[1]) * denominator(coords[2])

        c = gcd(x,y,z)

        #Eliminate gcd
        if c!= 1
          x = divexact(x, c)
          y = divexact(y, c)
          z = divexact(z, c)
        end

        P.coordx = K(x)
        P.coordy = K(y)
        P.coordz = K(z)
      end
    end
    return P
  end
end

function Base.getindex(P::ConCrvPt, i::Int)
  @req 1 <= i <= 3 "Index must be 1, 2 or 3"

  if i == 1
    return P.coordx
  elseif i == 2
    return P.coordy
  elseif i == 3
    return P.coordz
  end
end

################################################################################
#
#  Constructors for Conic Curve
#
################################################################################

@doc raw"""
    conic_curve([K::Field], x::Vector; check::Bool = true) -> ConCrv
Given x = [a11, a22, a33, a12, a23, a13] returns the conic given by
a11x^2 + a22y^2 + a33z^2 + a12xy + a23yz + a13xz.

If x contains only three elements, i.e x = [a11, a22, a33] returns the conic given by
a11x^2 + a22y^2 + a33z^2.
"""
function conic_curve(x::Vector{T}; check::Bool = true) where T <: RingElem
  return ConCrv{T}(x, check)
end

function conic_curve(K::Field, x::Vector{T}; check::Bool = true) where T 
  if T === elem_type(K)
    return conic_curve(x, check = check)
  else
    return conic_curve(elem_type(K)[K(z) for z in x], check = check)
  end
end

function conic_curve(f::MPolyRingElem{T}; check::Bool = true) where T <: RingElem
  R = parent(f)
  x, y, z = gens(R)
  L = [coeff(f, x^2), coeff(f, y^2), coeff(f, z^2), coeff(f, x*y), coeff(f, y*z), coeff(f, x*z) ]
  return ConCrv{T}(L, check)
end

function conic_curve(K::Field, f::MPolyRingElem{T}; check::Bool = true) where T <: RingElem
  R = parent(f)
  x, y, z = gens(R)
  L = map(K, [coeff(f, x^2), coeff(f, y^2), coeff(f, z^2), coeff(f, x*y), coeff(f, y*z), coeff(f, x*z) ])
  return conic_curve(L, check = check)

end

function conic_curve(M::MatElem{T}; check::Bool = true) where T 
  if !is_symmetric(M)
    error("Matrix is not symmetric.")
  end
  L = [M[1,1], M[2,2], M[3,3], 2*M[1,2], 2*M[2,3], 2*M[1,3]]
  return ConCrv{T}(L, check)
end

function conic_curve(K::Field, M::MatElem{T}; check::Bool = true) where T 
  if T === elem_type(K)
    return conic_curve(x, check = check)
  else
    return conic_curve(change_base_ring(K,M), check = check)
  end
end
################################################################################
#
#  Field access
#
################################################################################

@doc raw"""
    base_field(C::ConCrv) -> Field

Return the base field over which `C` is defined.
"""
function base_field(C::ConCrv{T}) where T
  return C.base_field::parent_type(T)
end

################################################################################
#
#  Base Change
#
################################################################################

@doc raw"""
    base_change(K::Field, C::ConCrv) -> ConicCurve

Return the base change of the conic curve $C$ over K if coercion is
possible.
"""
function base_change(K::Field, C::ConCrv)
  a11, a22, a33, a12, a23, a13 = coefficients(C)
  return ConicCurve(map(K, [a11, a22, a33, a12, a23, a13])::Vector{elem_type(K)})
end

################################################################################
#
#  Coefficients
#
################################################################################

@doc raw"""
    coefficients(C::ConicCurve{T}) -> Tuple{T, T, T, T, T, T}

Return the coefficients of $C$ as a tuple $(a_11, a_22, a_33, a_12, a_23, a_13)$
such that $C$ is given by $a_11x^2 + a_22y^2 + a_33z^2 + a_12xy + a_23yz + a_13xz$.
"""
function coefficients(C::ConCrv{T}) where T
  return C.coeffs
end

function matrix(C::ConCrv{QQFieldElem})
  a11, a22, a33, a12, a23, a13 = C.coeffs
  M = numerator(matrix(QQ, 3, 3, [a11, a12//2, a13//2, a12//2, a22, a23//2, a13//2, a23//2, a33]))
  return M
end

function matrix(C::ConCrv{T}) where T <: FieldElem
  a11, a22, a33, a12, a23, a13 = C.coeffs
  K = parent(a11)
  M = matrix(K, 3, 3, [a11, a12/2, a13/2, a12/2, a22, a23/2, a13/2, a23/2, a33])
  return M
end

################################################################################
#
#  Equality of Models
#
################################################################################

@doc raw"""
    ==(C::ConCrv, D::ConCrv) -> Bool

Return true if $C$ and $D$ are given by the same model over the same field.
"""
function ==(C::ConCrv{T}, D::ConCrv{T}) where T
  return coefficients(C) == coefficients(D) && base_field(C) == base_field(D)
end

function Base.hash(C::ConCrv, h::UInt)
  h = hash(base_field(C), h)
  h = hash(coefficients(C), h)
  return h
end

################################################################################
#
#  Genus
#
################################################################################

@doc raw"""
    genus(C::ConCrv{T}) -> T

Return the genus of $C$.
"""
function genus(C::ConCrv{T}) where T
  return 0
end



################################################################################
#
#  Discriminant
#
################################################################################

@doc raw"""
    discriminant(C::ConCrv{T}) -> T

Compute the discriminant of $C$.
"""
function discriminant(C::ConCrv{T}) where T
    return C.disc
end


################################################################################
#
#  Equations
#
################################################################################

@doc raw"""
    equation(C::ConCrv) -> Poly

Return the equation defining the conic curve C.
"""
function equation(C::ConCrv)
  K = base_field(C)
  Kxyz,(x,y,z) = polynomial_ring(K, ["x","y","z"])
  a11, a22, a33, a12, a23, a13 = C.coeffs
  f = a11*x^2 + a22*y^2 + a33*z^2 + a12*x*y + a23*y*z + a13*x*z

  return f
end


################################################################################
#
#  Points on Conic Curves
#
################################################################################

function (C::ConCrv{T})(coords::Vector{S}; check::Bool = true) where {S, T}
  if !(2 <= length(coords) <= 3)
    error("Points need to be given in either affine coordinates (x, y) or projective coordinates (x, y, z).")
  end

  if length(coords) == 2
    push!(coords, 1)
  end
  if S === T
    parent(coords[1]) != base_field(C) &&
        error("Objects must be defined over same field.")
    return ConCrvPt{T}(C, coords, check)
  else
    return ConCrvPt{T}(C, map(base_field(C), coords)::Vector{T}, check)
  end
end


function find_rational_point(C::ConCrv{QQFieldElem})
  #TODO: Use Hasse principle/Hilbert symbols to detect whether a solution exists or not. 
  #Currently it will either find something or throw an error.
  M = matrix(C)
  n = ncols(M)
  if det(M) == 0
    sol = kernel(M)[1,:]
    return C(vec(Array(sol)))
  end

  Cmin ,_, W = minimal_model(C)
  M = matrix(Cmin)

  B, U, sol = lll_gram_indef_isotropic(M; base = true)
  if length(sol) != 0
    return C(vec(Array(sol*transpose(W))))
  else
    error("Either no point exists or there is a bug in the code.")
  end
end

function find_rational_point(C::ConCrv{T}) where T<:Union{AbsSimpleNumFieldElem}
  K = base_field(C)
  Q = quadratic_space(K, matrix(C))
  bool, sol = is_isotropic_with_vector(Q)
  return C(sol)
end

function find_rational_point(C::ConCrv{FqFieldElem})
  K = base_field(C)
  Kt,t = polynomial_ring(K, "t")
  a11, a22, a33, a12, a23, a13 = C.coeffs
  while true
    x = rand(K)
    f = a11*x^2 + a22*t^2 + a33 + a12*x*t + a23*t + a13*x
    sols = roots(f)
    if length(sols) != 0
      y = sols[1]
      return C([x,y,K(1)])
    end
  end
end


function reduce_conic(v)
  a, b, c = v
  
  
  ad, bd, cd = map(denominator, [a,b,c])
  w = lcm([ad, bd, cd])
  a, b, c = map(x -> w*x, [a, b, c])
  a,b,c = map(numerator, [a,b,c])
  w = gcd(a,b,c)
  a, b, c = map(x -> x/w, [a, b, c])
  lambda = mu = nu =1
  g1 = g2 = g3 =-1
  while g1 != 1 || g2 != 1 || g3 != 1
    g1 = gcd(a,b)
    a = a/g1; b = b/g1; c = c*g1; nu = g1*nu
    g2 = gcd(a,c)
    a = a/g2; b = g2*b; c = c/g2; mu = g2*mu
    g3 = gcd(b,c)
    a = g3*a; b = b/g3; c = c/g3; lambda = g3*lambda
  end

  facs_a = factor_squarefree(a)
  facs_b = factor_squarefree(b)
  facs_c = factor_squarefree(c)
  Kt = parent(a)
  #Compute a1, a2
  a1 = facs_a.unit
  a2 = one(Kt)
  for (p,e) in facs_a
    f = mod(e,2)
    a1 *= p^f 
    a2 *= p^(e-f)
  end
  mu = a2 * mu
  nu = a2* nu 

  #Compute b1, b2
  b1 = facs_b.unit
  b2 = one(Kt)
  for (p,e) in facs_b
    f = mod(e,2)
    b1 *= p^f 
    b2 *= p^(e-f)
  end
  lambda = b2 * lambda
  nu = b2* nu 

  #Compute c1, c2
  c1 = facs_c.unit
  c2 = one(Kt)
  for (p,e) in facs_c
    f = mod(e,2)
    c1 *= p^f 
    c2 *= p^(e-f)
  end
  mu = c2 * mu
  lambda = c2* lambda

  return a1, b1, c1, lambda, mu, nu

end

function find_rational_point(conic::ConCrv{Generic.RationalFunctionFieldElem{S,T}}) where {S,T}
  Kt_FF = base_field(conic)
  K = base_ring(Kt_FF)
  t_FF = gen(Kt_FF)
  M1 = matrix(conic)
  M,  U = Hecke._gram_schmidt(M1, identity)
  
  a, b, c = diagonal(M)
  Kt = parent(a)
  t = gen(Kt)
  if iszero(a) 
    return conic([1,0,0])
  end

  if iszero(b) 
    return conic([0,1,0])
  end

  if iszero(c) 
    return conic([0,0,1])
  end

  a, b, c, lambda, mu, nu= reduce_conic([a,b,c])

  da, db, dc = map(degree, [a,b,c])

  supp_a = Set([p for (p,e) in factor(a)])
  supp_b = Set([p for (p,e) in factor(b)])
  supp_c = Set([p for (p,e) in factor(c)])

  #Determine case 
  case = 1
  if mod(da, 2) == mod(db, 2) == mod(dc, 2) == 0
    Supp = union(supp_a, supp_b, supp_c)
    case = 0
    for s in Supp
      if degree(s) == 1
        case = 1
        delete!(supp_a, s)
        delete!(supp_b, s)
        delete!(supp_c, s)
        break
      end
    end
  end 

  if case == 0
    la, lb, lc = map(leading_coefficient, [a,b,c])
    P = find_rational_point(conic_curve(K, [la,lb,lc]))
    sol_cert_0 = [P[1], P[2], P[3]]
  end
  Kt = parent(a)

  sol_cert = [[],[],[]]

  for p in supp_a
    Lp, phi = residue_field(Kt, p)
    Lpu, u = polynomial_ring(Lp, "u")
    fa = Lp(b) * u^2 + Lp(c)
    sols = roots(fa)
    if length(sols) == 0
      error("Conic contains no rational point.")
    else
      push!(sol_cert[1], [p, preimage(phi, sols[1])])
    end
  end

  for p in supp_b
    Lp, phi = residue_field(Kt, p)
    Lpu, u = polynomial_ring(Lp, "u")
    fb = Lp(c) * u^2 + Lp(a)
    sols = roots(fb)
    if length(sols) == 0
      error("Conic contains no rational point.")
    else
      push!(sol_cert[2], [p, preimage(phi, sols[1])])
    end
  end

    for p in supp_c
      Lp, phi = residue_field(Kt, p)
      Lpu, u = polynomial_ring(Lp, "u")
      fc = Lp(a) * u^2 + Lp(b)
      sols = roots(fc)
      if length(sols) == 0
        error("Conic contains no rational point.")
      else
        push!(sol_cert[3], [p, preimage(phi, sols[1])])
      end
    end
  

  #Shifted all by +1 as paper has i starting at 0.
  A = ceil(Int, (db + dc)/2) - case + 1
  B = ceil(Int, (dc + da)/2) - case + 1
  C = ceil(Int, (da + db)/2) - case + 1

  K = base_ring(Kt) 
  if case == 0
    FXYZ, XYZ = polynomial_ring(K, A + B + C + 1)
  else
    FXYZ, XYZ = polynomial_ring(K, A + B + C)
  end
  X = XYZ[(1:A)]
  Y = XYZ[(A+1:A+B)]
  Z = XYZ[(A+B+1:A+B+C)]

  FXYZt, tt = polynomial_ring(FXYZ, "t")


  X_ = sum(X[i]*tt^(i-1) for i in (1:A);init = zero(FXYZt))
  Y_ = sum(Y[i]*tt^(i-1) for i in (1:B);init = zero(FXYZt))
  Z_ = sum(Z[i]*tt^(i-1) for i in (1:C);init = zero(FXYZt))

  if case == 0 
    W = XYZ[end]
    E = [X[end] - sol_cert_0[1]*W, Y[end] - sol_cert_0[2]*W, Z[end] - sol_cert_0[3]*W]
  else
    E = []
  end
  
  
  for (p, alpha) in sol_cert[1]
    r = divrem(Y_ - evaluate(alpha,tt) * Z_, evaluate(p,tt))[2]
    for i in (0:degree(p)-1)
      push!(E, coeff(r, i))
    end
  end

  for (p, alpha) in sol_cert[2]
    r = divrem(Z_ - evaluate(alpha,tt) * X_, evaluate(p,tt))[2]
    for i in (0:degree(p)-1)
      push!(E, coeff(r, i))
    end
  end

  for (p, alpha) in sol_cert[3]
    r = divrem(X_ - evaluate(alpha,tt) * Y_, evaluate(p,tt))[2]
    for i in (0:degree(p)-1)
      push!(E, coeff(r, i))
    end
  end
  
  M = zero_matrix(K, length(gens(FXYZ)), length(E))
  for i in (1:length(E))
    for j in (1:length(gens(FXYZ)))
      M[j, i] = coeff(E[i],gens(FXYZ)[j])
    end
  end

  sol = kernel(M)[1, :]
  X_ = sum(sol[i]*t^(i-1) for i in (1:A);init = zero(Kt))
  Y_ = sum(sol[A+i]*t^(i-1) for i in (1:B);init = zero(Kt))
  Z_ = sum(sol[A+B+i]*t^(i-1) for i in (1:C);init = zero(Kt))
  
  return conic([lambda*X_, mu*Y_, nu*Z_]*U)
end



################################################################################
#
#  Minimal models
#
################################################################################


function minimal_model(C::ConCrv{QQFieldElem})
  M = matrix(C)

  detC = abs(det(M))
  detM = det(M)
  W = identity_matrix(ZZ,3)
  
  while abs(detM)!=1
    factors = factor(detM)
    for (p,e) in factors
      U, d = algorithm22(M,p)
      if valuation(detM, p) == 1
        V = algorithm26(M, U, p)
      elseif d==1
        V = algorithm211(M,U,p)
      else
        V = algorithm214(M, U, p)
      end

      W = W*V
      M = divexact(transpose(V) * M * V, det(V))
    end 
    detM = det(M)
  end
  K = base_field(C)
  Kxyz,(x,y,z) = polynomial_ring(K, ["x","y","z"]) 

  B, U, sol = lll_gram_indef_isotropic(M; base = true)

  W = W * transpose(U)
  W = W/content(W)
  #Return minimized conic Cmin, map from Cmin -> C, and corresponding matrix.
  return conic_curve(K, B), W * [x,y,z], W 

end

function algorithm22(M::ZZMatrix, p::ZZRingElem)
  n = ncols(M)
  i = n
  d = 0
  U = identity_matrix(ZZ, n)
  while i > 0
    j = i + d 
    
    while j > 0 && mod(M[i,j], p)==0
      j -= 1
    end

    if j == 0
      d+=1
      i-=1
      continue
    end
    
    if j < i + d
      M = swap_cols(M, j, i+d)
      U = swap_cols(U, j, i+d)
    end

    u = lift(ZZ, inv(GF(p)(M[i,i+d])))

    for k in (1:j-1)
      a = mod(u * M[i,k], p)
      M = add_column(M, -a, i+d, k)
      U = add_column(U, -a, i+d, k)
    end
    M = mod(M, p)
  i-=1
  end
  return U, d
end

function algorithm26(Q::ZZMatrix, U::ZZMatrix, p::ZZRingElem)
  Qnew = transpose(U) * Q * U
  if mod(Qnew[2,2], p) == 0
    N = matrix(ZZ, [[1,0,0],[0,1,0],[0,0,p]])
    return U*N
  end
  u = lift(ZZ, inv(GF(p)(Qnew[2,2])))
  t = Qnew[3,2]^2 - Qnew[2,2]*Qnew[3,3]
  if !is_square(GF(p)(t))
    error("No rational point exists.")
  end
  delta = sqrtmod(t,p)
  x = mod(u*(-Qnew[2,3] +delta),p)

  N = matrix(ZZ, [[1,0,0],[0,p,x],[0,0,1]])
  return U*N
end

function algorithm211(Q::ZZMatrix, U::ZZMatrix, p::ZZRingElem)
  Qnew = transpose(U) * Q * U
  N = matrix(ZZ, [[1,0,0],[0,p,0],[0,0,p]])
  return U*N
end

function algorithm214(Q::ZZMatrix, U::ZZMatrix, p::ZZRingElem)
  Qnew = transpose(U) * Q * U
  N = matrix(ZZ, [[1,0,0],[0,1,0],[0,0,p]])
  return U*N
end

function parametrization(C::ConCrv{QQFieldElem}, P::ConCrvPt{QQFieldElem})
  M = matrix(C)
  U = Hecke._complete_to_basis(matrix(ZZ,1, 3, [P[1], P[2], P[3]]))
  M1 = U * M * transpose(U)

  a = 2*M1[1,2]
  b = -2*M1[1,3]
  c = -2*M1[2,3]
  d = M1[1,1]
  e = M1[2,2]
  M2 = matrix(QQ, 3, 3, [b,c, 0, 0,b, c,d, a, e])
  T = transpose(U)*M2
  R, (u,v) = polynomial_ring(QQ, ["u","v"])
  X = T[1,1]*u^2 + T[1,2]*u*v +T[1,3]*v^2
  Y = T[2,1]*u^2 + T[2,2]*u*v + T[2,3]*v^2
  Z = T[3,1]*u^2 + T[3,2]*u*v +T[3,3]*v^2
  return X, Y, Z
end

function parametrization(C::ConCrv{QQFieldElem})
  P = find_rational_point(C)
  return parametrization(C, P)
end

################################################################################
#
#  Parent
#
################################################################################

function parent(P::ConCrvPt)
  return P.parent
end


################################################################################
#
#  Test for inclusion
#
################################################################################

@doc raw"""
    is_on_curve(C::ConCrv{T}, coords::Vector{T}) -> Bool

Return true if `coords` defines a point on $C$ and false otherwise. The array
`coords` must have length 2.
"""
function is_on_curve(C::ConCrv{T}, coords::Vector{T}) where T
  length(coords) != 3 && error("Array must be of length 3.")
  coords
  x = coords[1]
  y = coords[2]
  z = coords[3]

  K = parent(x)

  if all(i -> i == zero(K), [x,y,z])
    error("(0 : 0 : 0) is not a point in projective space.")
  end

  equ = equation(C)
  equ(x, y, z)
  if equ(x, y, z) == 0 
    return true
  else
    return false
  end
end

################################################################################
#
#  ElemType
#
################################################################################

function elem_type(::Type{ConCrv{T}}) where T
  return ConCrvPt{T}
end


################################################################################
#
#  String I/O
#
################################################################################

function show(io::IO, C::ConCrv)
  f = equation(C)
  print(io, "Conic curve with equation\n $(f)")
end

function show(io::IO, P::ConCrvPt)
   print(io, "Point  ($(P[1]) : $(P[2]) : $(P[3]))  of $(P.parent)")
end

@doc raw"""
    ==(P::ConCurvePoint, Q::ConCurvePoint) -> Bool

Return true if $P$ and $Q$ are equal and live over the same conic curve
$E$.
"""
function ==(P::ConCrvPt{T}, Q::ConCrvPt{T}) where T
  if parent(P) != parent(Q)
    return false
  end
  # Compare coordinates
  if P[1] == Q[1] && P[2] == Q[2] && P[3] == Q[3]
    return true
  else
    return false
  end
end

function Base.hash(P::ConCrvPt, h::UInt)
  h = hash(parent(P), h)
  h = hash(P[1], h)
  h = hash(P[2], h)
  h = hash(P[3], h)
  return h
end
