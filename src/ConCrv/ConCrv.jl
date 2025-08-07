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
    R = base_ring(f)
    if length(coeffs) == 3
      a11, a22, a33, a12, a23, a13 = Vector([coeffs[1], coeffs[2], coeffs[3], zero(T), zero(T), zero(T)])
    elseif length(coeffs) == 6
      a11, a22, a33, a12, a23, a13 = coeffs
    else
      error("Length of coefficient array must be either 3 or 6")
    end

    d = 4*a11 * a22 * a33 - a11 * a23^2 - a12^2 * a33 + a12 * a13 * a23 - a13^2 * a22
    if d != 0 && check
      C = new{T}()
      C.f = f
      C.base_field = R
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
        x = numerator(coords[1]) * denominator(coords[3])
        y = coords[2] * (denominator(coords[3]) * denominator(coords[1]))
        z = numerator(coords[3]) * denominator(coords[1])

        c = gcd(x, z)

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
    ConicCurve([K::Field]; check::Bool = true) -> ConCrv

Return the conic curve $y^2 + h(x)y = f(x)$. The polynomial $f$
must be monic of degree 2g + 1 > 3 or of degree 2g + 2 > 4 and the
polynomial h must be of degree < g + 2. Here g will be the genus of the curve.
"""
function ConicCurve(x::Vector{T}; check::Bool = true) where T <: FieldElem
  return ConCrv{T}(x, check)
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
function coefficients(C::ConCurve)
  return C.coeffs
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

function Base.hash(C::HypellCrv, h::UInt)
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
    return C.d
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
    error("Points need to be given in either affine coordinates (x, y) or projective coordinates (x, y, z)")
  end

  if length(coords) == 2
    push!(coords, 1)
  end
  if S === T
    parent(coords[1]) != base_field(C) &&
        error("Objects must be defined over same field")
    return ConCrvPt{T}(C, coords, check)
  else
    return ConCrvPt{T}(C, map(base_field(C), coords)::Vector{T}, check)
  end
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
  length(coords) != 3 && error("Array must be of length 3")
  coords
  x = coords[1]
  y = coords[2]
  z = coords[3]

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

function show(io::IO, C::HypellCrv)
  f = equation(C)
  print(io, "Conic curve of with equation\n $(f)")
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
