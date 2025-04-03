################################################################################
#
#          HypellCrv/HypellCrv.jl : Hyperelliptic curves over general fields
#
# (C) 2022 Jeroen Hanselman
#
################################################################################

################################################################################
#
#  Types
#
################################################################################

mutable struct HypellCrv{T}
  base_field::Ring
  f::PolyRingElem{T}
  h::PolyRingElem{T}
  f_hom::MPolyRingElem{T}
  h_hom::MPolyRingElem{T}
  g::Int
  disc::T

  function HypellCrv{T}(f::PolyRingElem{T}, h::PolyRingElem{T}, check::Bool = true) where {T}
    n = degree(f)
    m = degree(h)
    g = div(degree(f) - 1, 2)
    if g < 0
      error("Curve has to be of positive genus")
    end
    if m > g + 1
      error("h has to be of degree smaller than g + 2.")
    end
    R = base_ring(f)

    if characteristic(R) == 2
      check = false
    end

    d = 2^(4*g)*discriminant(f + divexact(h^2,4))

    if d != 0 && check
      C = new{T}()

      C.f = f
      C.h = h
      C.g = g
      C.disc = d
      C.base_field = R

      coeff_f = coefficients(f)
      coeff_h = coefficients(h)

      Rxz, (x, z) = polynomial_ring(R, ["x", "z"])
      f_hom = sum([coeff_f[i]*x^i*z^(2*g + 2 - i) for i in (0:n)];init = zero(Rxz))
      h_hom = sum([coeff_h[i]*x^i*z^(g + 1 - i) for i in (0:m)];init = zero(Rxz))
      C.f_hom = f_hom
      C.h_hom = h_hom

    else
      error("Discriminant is zero")
    end
    return C
  end
end

mutable struct HypellCrvPt{T}
  coordx::T
  coordy::T
  coordz::T
  is_infinite::Bool
  parent::HypellCrv{T}

  function HypellCrvPt{T}(C::HypellCrv{T}, coords::Vector{T}, check::Bool = true) where {T}
    g = genus(C)
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
      P.is_infinite = true
    else
      P.is_infinite = false

      #Don't have numerators, denominators and gcd over finite fields
      if T <: FinFieldElem

        scalar = inv(coords[3])

        P.coordx = coords[1]*scalar
        P.coordy = coords[2]*scalar^(g+1)
        P.coordz = coords[3]*scalar
      else

        #Eliminate denominators
        x = numerator(coords[1]) * denominator(coords[3])
        y = coords[2] * (denominator(coords[3]) * denominator(coords[1]))^(g + 1)
        z = numerator(coords[3]) * denominator(coords[1])

        c = gcd(x, z)

        #Eliminate gcd
        if c!= 1
          x = divexact(x, c)
          y = divexact(y, c^(g+1))
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

function Base.getindex(P::HypellCrvPt, i::Int)
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
#  Constructors for Hyperelliptic Curve
#
################################################################################

@doc raw"""
    HyperellipticCurve(f::PolyRingElem, g::PolyRingElem; check::Bool = true) -> HypellCrv

Return the hyperelliptic curve $y^2 + h(x)y = f(x)$. The polynomial $f$
must be monic of degree 2g + 1 > 3 or of degree 2g + 2 > 4 and the
polynomial h must be of degree < g + 2. Here g will be the genus of the curve.
"""
function HyperellipticCurve(f::PolyRingElem{T}, h::PolyRingElem{T}; check::Bool = true) where T <: FieldElem
  @req is_monic(f) "Polynomial must be monic"
  @req degree(f) >= 3 "Polynomial must be of degree bigger than 3"

  return HypellCrv{T}(f, h, check)
end

@doc raw"""
    HyperellipticCurve(f::PolyRingElem; check::Bool = true) -> HypellCrv

Return the hyperelliptic curve $y^2 = f(x)$. The polynomial $f$ must be monic of
degree larger than 3.
"""
function HyperellipticCurve(f::PolyRingElem{T}; check::Bool = true) where T <: FieldElem
  @req is_monic(f) "Polynomial must be monic"
  @req degree(f) >= 3 "Polynomial must be of degree bigger than 3"
  R = parent(f)
  return HypellCrv{T}(f, zero(R), check)
end


################################################################################
#
#  Field access
#
################################################################################

@doc raw"""
    base_field(C::HypellCrv) -> Field

Return the base field over which `C` is defined.
"""
function base_field(C::HypellCrv{T}) where T
  return C.base_field::parent_type(T)
end

################################################################################
#
#  Base Change
#
################################################################################

@doc raw"""
    base_change(K::Field, C::HypellCrv) -> EllipticCurve

Return the base change of the hyperelliptic curve $C$ over K if coercion is
possible.
"""
function base_change(K::Field, C::HypellCrv)
  f, h = hyperelliptic_polynomials(C)
  fnew = change_coefficient_ring(K, f)
  hnew = change_coefficient_ring(K, h)
  return HyperellipticCurve(fnew, hnew)
end


################################################################################
#
#  Equality of Models
#
################################################################################

@doc raw"""
    ==(C::HypellCrv, D::HypellCrv) -> Bool

Return true if $C$ and $D$ are given by the same model over the same field.
"""
function ==(C::HypellCrv{T}, D::HypellCrv{T}) where T
  return hyperelliptic_polynomials(C) == hyperelliptic_polynomials(D) && base_field(C) == base_field(D)
end

function Base.hash(C::HypellCrv, h::UInt)
  h = hash(base_field(C), h)
  h = hash(hyperelliptic_polynomials(C), h)
  return h
end

################################################################################
#
#  Genus
#
################################################################################

@doc raw"""
    genus(C::HypellCrv{T}) -> T

Return the of $C$.
"""
function genus(C::HypellCrv{T}) where T
  return C.g
end



################################################################################
#
#  Discriminant
#
################################################################################

@doc raw"""
    discriminant(C::HypellCrv{T}) -> T

Compute the discriminant of $C$.
"""
function discriminant(C::HypellCrv{T}) where T
  if isdefined(C, :disc)
    return C.disc
  end
  K = base_field(C)
  if characteristic(K) != 2
    f, h = hyperelliptic_polynomials(C)
    d = 2^(4*g)*discriminant(f(x) + 1//4*h(x)^2)
    C.disc = d
    return d::T
  else
    #Need to use Witt vectors for this
    error("Cannot compute discriminant of hyperelliptic curve in characteristic 2.")
  end
end


################################################################################
#
#  Equations
#
################################################################################

@doc raw"""
    equation(C::HypellCrv) -> Poly

Return the equation defining the hyperelliptic curve C.
"""
function equation(C::HypellCrv)
  K = base_field(C)
  Kxy,(x,y) = polynomial_ring(K, ["x","y"])

  f, h = hyperelliptic_polynomials(C)

  return y^2 + h(x)*y - f(x)
end

@doc raw"""
    homogeneous_equation(C::HypellCrv) -> Poly

Return the homogeneous equation defining the hyperelliptic curve C.
"""
function homogeneous_equation(C::HypellCrv)
  K = base_field(C)
  Kxyz, (x, y, z) = polynomial_ring(K, ["x", "y", "z"])

  f = C.f_hom
  h = C.h_hom

  return y^2 + h(x, z)*y - f(x, z)
end



@doc raw"""
    hyperelliptic_polynomials(C::HypellCrv) -> Poly, Poly

Return f, h such that C is given by y^2 + h*y = f
"""
function hyperelliptic_polynomials(C::HypellCrv{T}) where T
  return (C.f, C.h)::Tuple{dense_poly_type(T), dense_poly_type(T)}
end


################################################################################
#
#  Points on Hyperelliptic Curves
#
################################################################################

function (C::HypellCrv{T})(coords::Vector{S}; check::Bool = true) where {S, T}
  if !(2 <= length(coords) <= 3)
    error("Points need to be given in either affine coordinates (x, y) or projective coordinates (x, y, z)")
  end

  if length(coords) == 2
    push!(coords, 1)
  end
  if S === T
    parent(coords[1]) != base_field(C) &&
        error("Objects must be defined over same field")
    return HypellCrvPt{T}(C, coords, check)
  else
    return HypellCrvPt{T}(C, map(base_field(C), coords)::Vector{T}, check)
  end
end

################################################################################
#
#  Parent
#
################################################################################

function parent(P::HypellCrvPt)
  return P.parent
end

################################################################################
#
#  Point at infinity
#
################################################################################

@doc raw"""
    points_at_infinity(C::HypellCrv) -> HypellCrvPt

Return the points at infinity.
"""
function points_at_infinity(C::HypellCrv{T}) where T
  K = base_field(C)
  equ = homogeneous_equation(C)

  infi = HypellCrvPt{T}[]

  if equ(one(K),zero(K), zero(K)) == 0
    push!(infi, C([one(K),zero(K), zero(K)]))
  end

  if equ(one(K),one(K), zero(K)) == 0
    push!(infi, C([one(K),one(K), zero(K)]))
    if characteristic(K)!= 2
      push!(infi, C([one(K),- one(K), zero(K)]))
    end
  end

  return infi
end

function points_with_x_coordinate(C::HypellCrv{T}, x) where T<: FinFieldElem
  R = base_field(C)
  Ry, y = polynomial_ring(R,"y")
  equ = homogeneous_equation(C)
  f = equ(R(x), y, one(R))
  ys = roots(f)
  pts = []
   for yi in ys
     push!(pts, C([x, yi, one(R)]))
   end
  return pts
end

function points_with_x_coordinate(C::HypellCrv{T}, x) where T
  R = base_field(C)
  Ry, y = polynomial_ring(R,"y")
  equ = homogeneous_equation(C)
  f = equ(numerator(x), y, denominator(x))
  ys = roots(f)
  pts = []
   for yi in ys
     push!(pts, C([numerator(x), yi, denominator(x)]))
   end
  return pts
end


@doc raw"""
    is_finite(P::HypellCrvPt) -> Bool

Return true if P is not the point at infinity.
"""
function is_finite(P::HypellCrvPt)
  return !P.is_infinite
end

@doc raw"""
    is_infinite(P::HypellCrvPt) -> Bool

Return true if P is the point at infinity.
"""
function is_infinite(P::HypellCrvPt)
  return P.is_infinite
end


################################################################################
#
#  Test for inclusion
#
################################################################################

@doc raw"""
    is_on_curve(C::HypellCrv{T}, coords::Vector{T}) -> Bool

Return true if `coords` defines a point on $C$ and false otherwise. The array
`coords` must have length 2.
"""
function is_on_curve(C::HypellCrv{T}, coords::Vector{T}) where T
  length(coords) != 3 && error("Array must be of length 3")
  coords
  x = coords[1]
  y = coords[2]
  z = coords[3]

  equ = homogeneous_equation(C)
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

function elem_type(::Type{HypellCrv{T}}) where T
  return HypellCrvPt{T}
end

################################################################################
#
#  Invariants
#
################################################################################

function transvectant(f::MPolyRingElem{T}, g::MPolyRingElem{T}, k::Int) where T
  Kxy = parent(f)
  K = base_ring(Kxy)
  x, y = gens(Kxy)
  n = max(total_degree(f),k)
  m = max(total_degree(g),k)
  c = factorial(m-k) * factorial(n-k) // (factorial(m) * factorial(n))

  Omega, (dfx, dfy, dgx, dgy) = polynomial_ring(K, ["dfx", "dfy", "dgx", "dgy"])
  diff_op = c * (dfx * dgy - dfy * dgx)^k

  result = Kxy(0)
  for mon in monomials(diff_op)
    dfxy_part = derivative(derivative(f, x, degree(mon, dfx)), y, degree(mon, dfy))
    dgxy_part = derivative(derivative(g, x, degree(mon, dgx)), y, degree(mon, dgy))
    
    result += coeff(diff_op,mon) * dfxy_part * dgxy_part
  end
  return result
end

function derivative(f::MPolyRingElem{T}, x::MPolyRingElem{T}, n::Int) where T
  @req n>=0 "n needs to be non-zero."
  i = 0
  while n > i 
    f = derivative(f, x)
    i +=1
  end
return f
end

function clebsch_invariants(f::MPolyRingElem{T}) where T
  Kxy = parent(f)
  x, y = gens(Kxy)
  n = total_degree(f)
  @req 5 <= n <= 6 "Clebsch invariants are only defined for a curve of genus 2."

  i = transvectant(f, f, 4)
  delta = transvectant(i, i, 2)
  y1 = transvectant(f, i, 4)
  y2 = transvectant(i, y1, 2)
  y3 = transvectant(i, y2, 2)
  A = transvectant(f, f, 6)
  B = transvectant(i, i, 4)
  C = transvectant(i, delta, 4)
  D = transvectant(y3, y1, 2)

  return [A, B, C, D]
end 

function clebsch_invariants(f::PolyRingElem{T}) where T
  R = base_ring(f)
  Rxz, (x, z) = polynomial_ring(R, ["x", "z"])
  coeff_f = coefficients(f)
  d = degree(f)
  f_hom = sum([coeff_f[i]*x^i*z^(d - i) for i in (0:d)];init = zero(Rxz))
  return clebsch_invariants(f_hom)
end

function igusa_clebsch_invariants(f::PolyRingElem{T}) where T
  K = base_ring(f)
  if  characteristic(K) in [2,3,5]
    error("Characteristic of the field cannot be 2, 3 or 5.")
  end
    A, B, C, D = clebsch_invariants(f)
    return [-120*A, -720*A^2 + 6750*B, 8640*A^3 - 108000*A*B + 202500*C, -62208*A^5 + 972000*A^3*B + 1620000*A^2*C - 3037500*A*B^2 - 6075000 * B * C - 4556250 * D]
end

function igusa_invariants(f::PolyRingElem{T}, h::PolyRingElem{T}) where T
  K = base_ring(f)
  @req 5 <= degree(f) <= 6 "Igusa invariants are only defined for a curve of genus 2."
  if characteristic(K) == 2 
    a0, a1, a2, a3 = coefficients(h)
    b0, b1, b2, b3, b4, b5, b6 = coefficients(f)
    A = a0^2*a3^2 + a1^2*a2^2
    B = a0^4*a3^2*b6 + a0^3*a1*a3^2*b5 + a0^3*a2^2*a3*b5 + a0^3*a3^3*b3 +
   a0^2*a1^2*a2^2*b6 + a0^2*a1^2*a3^2*b4 + a0^2*a1*a2^3*b5 +
   a0^2*a1*a2*a3^2*b3 + a0^2*a2^3*a3*b3 + a0^2*a2^2*a3^2*b2 +
   a0^2*a2*a3^3*b1 + a0^2*a3^4*b0 + a0^2*a3^2*b3^2 + a0*a1^4*a3*b5 +
   a0*a1^3*a2^2*b5 + a0*a1^3*a3^2*b3 + a0*a1^2*a2^2*a3*b3 + a0*a1^2*a3^3*b1 +
   a0*a1*a2^4*b3 + a0*a2^4*a3*b1 + a1^5*a2*b5 + a1^4*a2^2*b4 +
   a1^4*a2*a3*b3 + a1^3*a2^3*b3 + a1^3*a2*a3^2*b1 + a1^2*a2^4*b2 +
   a1^2*a2^3*a3*b1 + a1^2*a2^2*a3^2*b0 + a1^2*a2^2*b3^2 + a1*a2^5*b1
   C = a0^6*a3^2*b6^2 + a0^4*a1^2*a2^2*b6^2 + a0^4*a1^2*a3^2*b5^2 +
   a0^4*a2^4*b5^2 + a0^4*a3^4*b3^2 + a0^2*a1^4*a2^2*b5^2 +
   a0^2*a1^4*a3^2*b4^2 + a0^2*a2^6*b3^2 + a0^2*a2^4*a3^2*b2^2 +
   a0^2*a2^2*a3^4*b1^2 + a0^2*a3^6*b0^2 + a0^2*a3^2*b3^4 + a1^8*b5^2 +
   a1^6*a2^2*b4^2 + a1^6*a3^2*b3^2 + a1^4*a2^4*b3^2 + a1^4*a3^4*b1^2 +
   a1^2*a2^6*b2^2 + a1^2*a2^4*a3^2*b1^2 + a1^2*a2^2*a3^4*b0^2 +
   a1^2*a2^2*b3^4 + a2^8*b1^2
   D = a0^8*a3^4*b6^2 + a0^8*a3^2*b6^3 + a0^8*b6^4 + a0^7*a1*a3^2*b5*b6^2 +
   a0^7*a2^2*a3^3*b5*b6 + a0^7*a2^2*a3*b5*b6^2 +  a0^7*a2*a3^4*b5^2 +
   a0^7*a3^5*b4*b5 + a0^7*a3^3*b3*b6^2 + a0^7*a3^3*b5^3 +
   a0^6*a1^2*a2^2*b6^3 + a0^6*a1^2*a3^2*b4*b6^2 + a0^6*a1^2*a3^2*b5^2*b6 +
   a0^6*a1*a2^3*a3^2*b5*b6 + a0^6*a1*a2^3*b5*b6^2 + a0^6*a1*a2^2*a3^3*b5^2 +
   a0^6*a1*a2*a3^4*b4*b5 + a0^6*a1*a2*a3^2*b3*b6^2 + a0^6*a1*a2*a3^2*b5^3 +
   a0^6*a1*a3^5*b3*b5 + a0^6*a2^6*b6^2 + a0^6*a2^5*a3*b5*b6 +
   a0^6*a2^4*a3^2*b4*b6 + a0^6*a2^4*a3^2*b5^2 + a0^6*a2^3*a3^3*b3*b6 +
   a0^6*a2^3*a3*b3*b6^2 + a0^6*a2^2*a3^4*b2*b6 + a0^6*a2^2*a3^4*b3*b5 +
   a0^6*a2^2*a3^2*b2*b6^2 + a0^6*a2*a3^5*b2*b5 + a0^6*a2*a3^5*b3*b4 +
   a0^6*a2*a3^3*b1*b6^2 + a0^6*a2*a3^3*b3*b5^2 + a0^6*a3^6*b1*b5 +
   a0^6*a3^6*b2*b4 + a0^6*a3^6*b3^2 + a0^6*a3^4*b0*b6^2 + a0^6*a3^4*b2*b5^2 +
   a0^6*a3^4*b3^2*b6 + a0^6*a3^2*b3^2*b6^2 + a0^5*a1^4*a3^3*b5*b6 +
   a0^5*a1^4*a3*b5*b6^2 + a0^5*a1^3*a2^2*b5*b6^2 + a0^5*a1^3*a3^2*b3*b6^2 +
   a0^5*a1^3*a3^2*b5^3 +  a0^5*a1^2*a2^3*a3^2*b5^2 +
   a0^5*a1^2*a2^2*a3^3*b4*b5 + a0^5*a1^2*a2^2*a3*b3*b6^2 +
   a0^5*a1^2*a2*a3^4*b3*b5 + a0^5*a1^2*a3^5*b2*b5 + a0^5*a1^2*a3^3*b1*b6^2 +
   a0^5*a1^2*a3^3*b3*b5^2 + a0^5*a1*a2^6*b5*b6 + a0^5*a1*a2^5*a3*b5^2 +
   a0^5*a1*a2^4*a3^2*b4*b5 + a0^5*a1*a2^4*b3*b6^2 + a0^5*a1*a2^3*a3^3*b3*b5 +
   a0^5*a1*a2^2*a3^4*b1*b6 + a0^5*a1*a2^2*a3^4*b3*b4 +
   a0^5*a1*a2^2*a3^2*b3*b5^2 + a0^5*a1*a2*a3^5*b1*b5 + a0^5*a1*a2*a3^5*b3^2 +
   a0^5*a1*a3^6*b1*b4 + a0^5*a1*a3^6*b2*b3 + a0^5*a1*a3^4*b1*b5^2 +
   a0^5*a1*a3^4*b3^2*b5 + a0^5*a2^7*b5^2 + a0^5*a2^6*a3*b3*b6 +
   a0^5*a2^6*a3*b4*b5 + a0^5*a2^5*a3^2*b3*b5 + a0^5*a2^4*a3^3*b3*b4 +
   a0^5*a2^4*a3*b1*b6^2 + a0^5*a2^3*a3^4*b1*b5 + a0^5*a2^2*a3^5*b1*b4 +
   a0^5*a2^2*a3^3*b1*b5^2 + a0^5*a2^2*a3^3*b3^2*b5 + a0^5*a2*a3^6*b1*b3 +
   a0^5*a3^7*b1*b2 + a0^5*a3^5*b3^3 + a0^4*a1^5*a2*a3^2*b5*b6 +
   a0^4*a1^5*a2*b5*b6^2 + a0^4*a1^5*a3^3*b5^2 + a0^4*a1^4*a2^2*b4*b6^2 +
   a0^4*a1^4*a2^2*b5^2*b6 + a0^4*a1^4*a2*a3^3*b3*b6 +
   a0^4*a1^4*a2*a3*b3*b6^2 + a0^4*a1^4*a3^4*b2*b6 + a0^4*a1^4*a3^4*b3*b5 +
   a0^4*a1^4*a3^4*b4^2 + a0^4*a1^4*a3^2*b4^2*b6 + a0^4*a1^4*a3^2*b4*b5^2 +
   a0^4*a1^4*b5^4 + a0^4*a1^3*a2^3*a3^2*b4*b5 + a0^4*a1^3*a2^3*b3*b6^2 +
   a0^4*a1^3*a2^2*a3^3*b3*b5 + a0^4*a1^3*a2*a3^4*b2*b5 +
   a0^4*a1^3*a2*a3^2*b1*b6^2 + a0^4*a1^3*a2*a3^2*b3*b5^2 +
   a0^4*a1^3*a3^5*b1*b5 + a0^4*a1^2*a2^6*b4*b6 + a0^4*a1^2*a2^5*a3*b4*b5 +
   a0^4*a1^2*a2^4*a3^2*b3*b5 + a0^4*a1^2*a2^4*a3^2*b4^2 +
   a0^4*a1^2*a2^4*b2*b6^2 + a0^4*a1^2*a2^3*a3^3*b3*b4 +
   a0^4*a1^2*a2^3*a3*b1*b6^2 + a0^4*a1^2*a2^2*a3^4*b0*b6 +
   a0^4*a1^2*a2^2*a3^4*b3^2 + a0^4*a1^2*a2^2*a3^2*b0*b6^2 +
   a0^4*a1^2*a2^2*a3^2*b2*b5^2 + a0^4*a1^2*a2^2*b3^2*b6^2 +
   a0^4*a1^2*a2*a3^5*b0*b5 + a0^4*a1^2*a2*a3^5*b2*b3 +
   a0^4*a1^2*a2*a3^3*b1*b5^2 + a0^4*a1^2*a3^6*b0*b4 +
   a0^4*a1^2*a3^6*b1*b3 + a0^4*a1^2*a3^4*b3^2*b4 +
   a0^4*a1^2*a3^2*b3^2*b5^2 + a0^4*a1*a2^7*b3*b6 + a0^4*a1*a2^7*b4*b5 +
   a0^4*a1*a2^5*a3^2*b3*b4 + a0^4*a1*a2^5*b1*b6^2 + a0^4*a1*a2^4*a3^3*b3^2 +
   a0^4*a1*a2^3*a3^4*b1*b4 + a0^4*a1*a2^3*a3^2*b1*b5^2 +
   a0^4*a1*a2^3*a3^2*b3^2*b5 + a0^4*a1*a2^2*a3^5*b1*b3 +
   a0^4*a1*a2*a3^6*b1*b2 + a0^4*a1*a2*a3^4*b3^3 + a0^4*a1*a3^7*b1^2 +
   a0^4*a2^8*b4^2 + a0^4*a2^7*a3*b1*b6 + a0^4*a2^7*a3*b2*b5 +
   a0^4*a2^7*a3*b3*b4 + a0^4*a2^6*a3^2*b0*b6 + a0^4*a2^6*a3^2*b2*b4 +
   a0^4*a2^6*a3^2*b3^2 + a0^4*a2^5*a3^3*b0*b5 + a0^4*a2^5*a3^3*b1*b4 +
   a0^4*a2^5*a3*b3^2*b5 + a0^4*a2^4*a3^4*b0*b4 + a0^4*a2^4*a3^4*b1*b3 +
   a0^4*a2^4*a3^4*b2^2 + a0^4*a2^4*a3^2*b2^2*b6 + a0^4*a2^4*a3^2*b3^2*b4 +
   a0^4*a2^3*a3^3*b3^3 + a0^4*a2^2*a3^4*b2*b3^2 + a0^4*a2*a3^5*b1^2*b5 +
   a0^4*a2*a3^5*b1*b3^2 + a0^4*a3^8*b0^2 + a0^4*a3^6*b0^2*b6 +
   a0^4*a3^6*b0*b3^2 + a0^4*a3^6*b1^2*b4 + a0^4*a3^4*b1^2*b5^2 +
   a0^4*a3^4*b3^4 + a0^4*a3^2*b3^4*b6 + a0^3*a1^6*a2^2*a3*b5*b6 +
   a0^3*a1^6*a2*a3^2*b5^2 + a0^3*a1^6*a3^3*b4*b5 + a0^3*a1^6*a3*b5^3 +
   a0^3*a1^5*a2^2*a3^2*b3*b6 + a0^3*a1^5*a2^2*b5^3 +
   a0^3*a1^5*a2*a3^3*b3*b5 + a0^3*a1^5*a3^4*b1*b6 + a0^3*a1^5*a3^4*b2*b5 +
   a0^3*a1^5*a3^2*b3*b5^2 + a0^3*a1^5*a3^2*b4^2*b5 +
   a0^3*a1^4*a2^3*a3^2*b3*b5 + a0^3*a1^4*a2^2*a3^3*b1*b6 +
   a0^3*a1^4*a2^2*a3^3*b2*b5 + a0^3*a1^4*a2^2*a3*b3*b5^2 +
   a0^3*a1^4*a2^2*a3*b4^2*b5 + a0^3*a1^4*a2*a3^4*b3^2 +
   a0^3*a1^4*a3^5*b2*b3 + a0^3*a1^4*a3^3*b1*b5^2 + a0^3*a1^4*a3^3*b3*b4^2 +
   a0^3*a1^3*a2^6*b3*b6 + a0^3*a1^3*a2^5*a3*b3*b5 +
   a0^3*a1^3*a2^4*a3^2*b3*b4 + a0^3*a1^3*a2^3*a3^3*b3^2 +
   a0^3*a1^3*a2^2*a3^4*b2*b3 + a0^3*a1^3*a2*a3^5*b1*b3 +
   a0^3*a1^3*a3^6*b0*b3 + a0^3*a1^3*a3^4*b3^3 + a0^3*a1^2*a2^7*b3*b5 +
   a0^3*a1^2*a2^6*a3*b1*b6 + a0^3*a1^2*a2^6*a3*b2*b5 +
   a0^3*a1^2*a2^4*a3^3*b0*b5 + a0^3*a1^2*a2^4*a3^3*b1*b4 +
   a0^3*a1^2*a2^3*a3^4*b1*b3 + a0^3*a1^2*a2^2*a3^5*b1*b2 +
   a0^3*a1^2*a2*a3^6*b1^2 + a0^3*a1^2*a3^7*b0*b1 + a0^3*a1^2*a3^5*b1^2*b5 +
   a0^3*a1^2*a3^5*b1*b3^2 + a0^3*a1*a2^8*b1*b6 + a0^3*a1*a2^8*b2*b5 +
   a0^3*a1*a2^8*b3*b4 + a0^3*a1*a2^7*a3*b3^2 + a0^3*a1*a2^6*a3^2*b2*b3 +
   a0^3*a1*a2^6*b3^2*b5 + a0^3*a1*a2^5*a3^3*b1*b3 +
   a0^3*a1*a2^4*a3^4*b0*b3 + a0^3*a1*a2^4*a3^2*b2^2*b5 +
   a0^3*a1*a2^2*a3^4*b1^2*b5 + a0^3*a1*a3^6*b0^2*b5 + a0^3*a1*a3^6*b1^2*b3 +
   a0^3*a1*a3^2*b3^4*b5 + a0^3*a2^9*b3^2 + a0^3*a2^8*a3*b0*b5 +
   a0^3*a2^8*a3*b1*b4 + a0^3*a2^8*a3*b2*b3 + a0^3*a2^7*a3^2*b1*b3 +
   a0^3*a2^6*a3^3*b1*b2 + a0^3*a2^6*a3*b2^2*b5 + a0^3*a2^6*a3*b3^3 +
   a0^3*a2^5*a3^4*b1^2 + a0^3*a2^4*a3^5*b0*b1 + a0^3*a2^4*a3^3*b1^2*b5 +
   a0^3*a2^4*a3^3*b2^2*b3 + a0^3*a2^2*a3^5*b0^2*b5 +
   a0^3*a2^2*a3^5*b1^2*b3 + a0^3*a2^2*a3*b3^4*b5 + a0^3*a3^7*b0^2*b3 +
   a0^3*a3^7*b1^3 + a0^3*a3^3*b3^5 + a0^2*a1^8*a2^2*b6^2 +
   a0^2*a1^8*a2*a3*b5*b6 + a0^2*a1^8*a3^2*b4*b6 + a0^2*a1^8*a3^2*b5^2 +
   a0^2*a1^7*a2^3*b5*b6 + a0^2*a1^7*a2^2*a3*b5^2 + a0^2*a1^7*a2*a3^2*b4*b5 +
   a0^2*a1^7*a2*b5^3 + a0^2*a1^7*a3^3*b3*b5 + a0^2*a1^6*a2^3*a3*b3*b6 +
   a0^2*a1^6*a2^2*a3^2*b3*b5 + a0^2*a1^6*a2^2*b4^2*b6 +
   a0^2*a1^6*a2^2*b4*b5^2 + a0^2*a1^6*a2*a3^3*b3*b4 +
   a0^2*a1^6*a2*a3*b3*b5^2 + a0^2*a1^6*a3^4*b0*b6 + a0^2*a1^6*a3^4*b2*b4 +
   a0^2*a1^6*a3^4*b3^2 + a0^2*a1^6*a3^2*b3^2*b6 + a0^2*a1^6*a3^2*b4^3 +
   a0^2*a1^5*a2^3*a3^2*b1*b6 + a0^2*a1^5*a2^3*a3^2*b2*b5 +
   a0^2*a1^5*a2^3*b3*b5^2 + a0^2*a1^5*a2^3*b4^2*b5 +
   a0^2*a1^5*a2*a3^4*b2*b3 + a0^2*a1^5*a2*a3^2*b1*b5^2 +
   a0^2*a1^5*a2*a3^2*b3*b4^2 + a0^2*a1^5*a3^5*b1*b3 +
   a0^2*a1^4*a2^6*b2*b6 + a0^2*a1^4*a2^5*a3*b2*b5 +
   a0^2*a1^4*a2^4*a3^2*b1*b5 + a0^2*a1^4*a2^4*a3^2*b2*b4 +
   a0^2*a1^4*a2^4*b3^2*b6 + a0^2*a1^4*a2^3*a3^3*b2*b3 +
   a0^2*a1^4*a2^3*a3*b1*b5^2 + a0^2*a1^4*a2^3*a3*b3*b4^2 +
   a0^2*a1^4*a2^2*a3^4*b1*b3 + a0^2*a1^4*a2^2*a3^4*b2^2 +
   a0^2*a1^4*a2^2*a3^2*b0*b5^2 + a0^2*a1^4*a2^2*a3^2*b2*b4^2 +
   a0^2*a1^4*a2^2*b3^2*b5^2 + a0^2*a1^4*a2*a3^5*b1*b2 +
   a0^2*a1^4*a2*a3^3*b1*b4^2 + a0^2*a1^4*a3^6*b0*b2 + a0^2*a1^4*a3^6*b1^2 +
   a0^2*a1^4*a3^4*b0*b4^2 + a0^2*a1^4*a3^4*b2*b3^2 +
   a0^2*a1^4*a3^2*b3^2*b4^2 + a0^2*a1^3*a2^7*b1*b6 + a0^2*a1^3*a2^7*b2*b5 +
   a0^2*a1^3*a2^5*a3^2*b0*b5 + a0^2*a1^3*a2^5*a3^2*b1*b4 +
   a0^2*a1^3*a2^4*a3^3*b1*b3 + a0^2*a1^3*a2^3*a3^4*b1*b2 +
   a0^2*a1^3*a2^2*a3^5*b1^2 + a0^2*a1^3*a2*a3^6*b0*b1 +
   a0^2*a1^3*a2*a3^4*b1^2*b5 + a0^2*a1^3*a2*a3^4*b1*b3^2 +
   a0^2*a1^2*a2^8*b0*b6 + a0^2*a1^2*a2^8*b2*b4 + a0^2*a1^2*a2^7*a3*b2*b3 +
   a0^2*a1^2*a2^6*a3^2*b1*b3 + a0^2*a1^2*a2^6*b2^2*b6 +
   a0^2*a1^2*a2^6*b3^2*b4 + a0^2*a1^2*a2^5*a3^3*b0*b3 +
   a0^2*a1^2*a2^4*a3^2*b1^2*b6 + a0^2*a1^2*a2^4*a3^2*b2^2*b4 +
   a0^2*a1^2*a2^2*a3^4*b0^2*b6 + a0^2*a1^2*a2^2*a3^4*b1^2*b4 +
   a0^2*a1^2*a2^2*b3^4*b6 + a0^2*a1^2*a2*a3^5*b1^2*b3 +
   a0^2*a1^2*a3^6*b0^2*b4 + a0^2*a1^2*a3^2*b3^4*b4 + a0^2*a1*a2^9*b0*b5 +
   a0^2*a1*a2^9*b1*b4 + a0^2*a1*a2^9*b2*b3 + a0^2*a1*a2^7*a3^2*b1*b2 +
   a0^2*a1*a2^7*b2^2*b5 + a0^2*a1*a2^7*b3^3 + a0^2*a1*a2^6*a3^3*b1^2 +
   a0^2*a1*a2^5*a3^4*b0*b1 + a0^2*a1*a2^5*a3^2*b1^2*b5 +
   a0^2*a1*a2^5*a3^2*b2^2*b3 + a0^2*a1*a2^3*a3^4*b0^2*b5 +
   a0^2*a1*a2^3*a3^4*b1^2*b3 + a0^2*a1*a2^3*b3^4*b5 +
   a0^2*a1*a2*a3^6*b0^2*b3 + a0^2*a1*a2*a3^6*b1^3 + a0^2*a1*a2*a3^2*b3^5 +
   a0^2*a2^10*b2^2 + a0^2*a2^9*a3*b0*b3 + a0^2*a2^9*a3*b1*b2 +
   a0^2*a2^8*a3^2*b0*b2 + a0^2*a2^8*a3^2*b1^2 + a0^2*a2^7*a3*b1*b3^2 +
   a0^2*a2^7*a3*b2^2*b3 + a0^2*a2^6*a3^2*b0*b3^2 + a0^2*a2^6*a3^2*b2^3 +
   a0^2*a2^6*b3^4 + a0^2*a2^5*a3^3*b1^2*b3 + a0^2*a2^5*a3^3*b1*b2^2 +
   a0^2*a2^4*a3^4*b0*b2^2 + a0^2*a2^4*a3^4*b1^2*b2 +
   a0^2*a2^4*a3^2*b2^2*b3^2 + a0^2*a2^3*a3^5*b0^2*b3 + a0^2*a2^3*a3^5*b1^3 +
   a0^2*a2^3*a3*b3^5 + a0^2*a2^2*a3^6*b0^2*b2 + a0^2*a2^2*a3^6*b0*b1^2 +
   a0^2*a2^2*a3^4*b1^2*b3^2 + a0^2*a2^2*a3^2*b2*b3^4 +
   a0^2*a2*a3^7*b0^2*b1 + a0^2*a2*a3^3*b1*b3^4 + a0^2*a3^8*b0^3 +
   a0^2*a3^6*b0^2*b3^2 + a0^2*a3^4*b0*b3^4 + a0^2*a3^2*b3^6 +
   a0*a1^10*a3*b5*b6 + a0*a1^9*a2^2*b5*b6 + a0*a1^9*a2*a3*b5^2 +
   a0*a1^9*a3^2*b3*b6 + a0*a1^9*a3^2*b4*b5 + a0*a1^8*a2^2*a3*b3*b6 +
   a0*a1^8*a3^3*b1*b6 + a0*a1^8*a3^3*b2*b5 + a0*a1^8*a3^3*b3*b4 +
   a0*a1^8*a3*b4^2*b5 + a0*a1^7*a2^4*b3*b6 + a0*a1^7*a2^3*a3*b3*b5 +
   a0*a1^7*a2^2*a3^2*b3*b4 + a0*a1^7*a2^2*b4^2*b5 + a0*a1^7*a2*a3^3*b3^2 +
   a0*a1^7*a3^4*b0*b5 + a0*a1^7*a3^4*b1*b4 + a0*a1^7*a3^4*b2*b3 +
   a0*a1^7*a3^2*b3^2*b5 + a0*a1^7*a3^2*b3*b4^2 + a0*a1^6*a2^4*a3*b1*b6 +
   a0*a1^6*a2^2*a3^3*b0*b5 + a0*a1^6*a2^2*a3^3*b1*b4 +
   a0*a1^6*a2^2*a3*b3^2*b5 + a0*a1^6*a2^2*a3*b3*b4^2 + a0*a1^6*a3^5*b0*b3 +
   a0*a1^6*a3^5*b1*b2 + a0*a1^6*a3^3*b1*b4^2 + a0*a1^6*a3^3*b3^3 +
   a0*a1^5*a2^6*b1*b6 + a0*a1^5*a2^5*a3*b1*b5 + a0*a1^5*a2^4*a3^2*b1*b4 +
   a0*a1^5*a2^4*b1*b5^2 + a0*a1^5*a2^4*b3^2*b5 + a0*a1^5*a2^4*b3*b4^2 +
   a0*a1^5*a2^3*a3^3*b1*b3 + a0*a1^5*a2^2*a3^4*b1*b2 +
   a0*a1^5*a2*a3^5*b1^2 + a0*a1^5*a3^6*b0*b1 + a0*a1^5*a3^4*b1*b3^2 +
   a0*a1^4*a2^7*b1*b5 + a0*a1^4*a2^6*a3*b0*b5 + a0*a1^4*a2^4*a3*b1*b4^2 +
   a0*a1^4*a2^4*a3*b2^2*b5 + a0*a1^4*a2^4*a3*b3^3 + a0*a1^4*a3^5*b0^2*b5 +
   a0*a1^4*a3*b3^4*b5 + a0*a1^3*a2^8*b0*b5 + a0*a1^3*a2^8*b1*b4 +
   a0*a1^3*a2^7*a3*b1*b3 + a0*a1^3*a2^6*a3^2*b0*b3 + a0*a1^3*a2^6*b2^2*b5 +
   a0*a1^3*a2^6*b3^3 + a0*a1^3*a2^4*a3^2*b1^2*b5 +
   a0*a1^3*a2^4*a3^2*b2^2*b3 + a0*a1^3*a2^2*a3^4*b0^2*b5 +
   a0*a1^3*a2^2*b3^4*b5 + a0*a1^3*a3^6*b0^2*b3 + a0*a1^3*a3^2*b3^5 +
   a0*a1^2*a2^9*b1*b3 + a0*a1^2*a2^8*a3*b0*b3 + a0*a1^2*a2^7*a3^2*b1^2 +
   a0*a1^2*a2^6*a3^3*b0*b1 + a0*a1^2*a2^6*a3*b1*b3^2 +
   a0*a1^2*a2^6*a3*b2^2*b3 + a0*a1^2*a2^4*a3^3*b1^2*b3 +
   a0*a1^2*a2^4*a3^3*b1*b2^2 + a0*a1^2*a2^2*a3^5*b0^2*b3 +
   a0*a1^2*a2^2*a3*b3^5 + a0*a1^2*a3^7*b0^2*b1 + a0*a1^2*a3^3*b1*b3^4 +
   a0*a1*a2^10*b0*b3 + a0*a1*a2^10*b1*b2 + a0*a1*a2^9*a3*b1^2 +
   a0*a1*a2^8*a3^2*b0*b1 + a0*a1*a2^8*b1*b3^2 + a0*a1*a2^8*b2^2*b3 +
   a0*a1*a2^6*a3^2*b1^2*b3 + a0*a1*a2^4*a3^4*b0^2*b3 + a0*a1*a2^4*b3^5 +
   a0*a2^11*b1^2 + a0*a2^10*a3*b0*b1 + a0*a2^8*a3*b1*b2^2 +
   a0*a2^6*a3^3*b1^3 + a0*a2^4*a3^5*b0^2*b1 + a0*a2^4*a3*b1*b3^4 +
   a1^12*b6^2 + a1^11*a2*b5*b6 + a1^11*a3*b5^2 + a1^10*a2^2*b4*b6 +
   a1^10*a2*a3*b3*b6 + a1^10*a2*a3*b4*b5 + a1^10*a3^2*b4^2 +
   a1^9*a2^3*b3*b6 + a1^9*a2^2*a3*b3*b5 + a1^9*a2*a3^2*b1*b6 +
   a1^9*a2*a3^2*b2*b5 + a1^9*a2*a3^2*b3*b4 + a1^9*a2*b4^2*b5 +
   a1^9*a3^3*b3^2 + a1^8*a2^4*b2*b6 + a1^8*a2^3*a3*b1*b6 +
   a1^8*a2^3*a3*b2*b5 + a1^8*a2^2*a3^2*b0*b6 + a1^8*a2^2*a3^2*b2*b4 +
   a1^8*a2^2*b3^2*b6 + a1^8*a2^2*b4^3 + a1^8*a2*a3^3*b0*b5 +
   a1^8*a2*a3^3*b1*b4 + a1^8*a2*a3^3*b2*b3 + a1^8*a2*a3*b3^2*b5 +
   a1^8*a2*a3*b3*b4^2 + a1^8*a3^4*b2^2 + a1^8*b4^4 + a1^7*a2^5*b1*b6 +
   a1^7*a2^4*a3*b1*b5 + a1^7*a2^3*a3^2*b0*b5 + a1^7*a2^3*a3^2*b1*b4 +
   a1^7*a2^3*b3^2*b5 + a1^7*a2^3*b3*b4^2 + a1^7*a2^2*a3^3*b1*b3 +
   a1^7*a2*a3^4*b0*b3 + a1^7*a2*a3^4*b1*b2 + a1^7*a2*a3^2*b1*b4^2 +
   a1^7*a2*a3^2*b3^3 + a1^7*a3^5*b1^2 + a1^6*a2^6*b0*b6 +
   a1^6*a2^5*a3*b0*b5 + a1^6*a2^4*a3^2*b0*b4 + a1^6*a2^4*b0*b5^2 +
   a1^6*a2^4*b2*b4^2 + a1^6*a2^4*b3^2*b4 + a1^6*a2^3*a3^3*b0*b3 +
   a1^6*a2^3*a3*b1*b4^2 + a1^6*a2^3*a3*b3^3 + a1^6*a2^2*a3^4*b0*b2 +
   a1^6*a2^2*a3^2*b0*b4^2 + a1^6*a2^2*a3^2*b2*b3^2 + a1^6*a2^2*b3^2*b4^2 +
   a1^6*a2*a3^5*b0*b1 + a1^6*a2*a3^3*b1*b3^2 + a1^6*a3^6*b0^2 +
   a1^6*a3^2*b3^4 + a1^5*a2^7*b0*b5 + a1^5*a2^5*b1*b4^2 +
   a1^5*a2^5*b2^2*b5 + a1^5*a2^5*b3^3 + a1^5*a2*a3^4*b0^2*b5 +
   a1^5*a2*b3^4*b5 + a1^4*a2^8*b0*b4 + a1^4*a2^7*a3*b0*b3 +
   a1^4*a2^6*b1^2*b6 + a1^4*a2^6*b2^2*b4 + a1^4*a2^6*b2*b3^2 +
   a1^4*a2^5*a3*b1^2*b5 + a1^4*a2^5*a3*b1*b3^2 + a1^4*a2^5*a3*b2^2*b3 +
   a1^4*a2^4*a3^2*b0*b3^2 + a1^4*a2^4*b1^2*b5^2 + a1^4*a2^2*a3^4*b0^2*b4 +
   a1^4*a2^2*b3^4*b4 + a1^4*a2*a3^5*b0^2*b3 + a1^4*a2*a3*b3^5 +
   a1^3*a2^9*b0*b3 + a1^3*a2^7*a3^2*b0*b1 + a1^3*a2^7*b1*b3^2 +
   a1^3*a2^7*b2^2*b3 + a1^3*a2^5*a3^2*b1^2*b3 + a1^3*a2^5*a3^2*b1*b2^2 +
   a1^3*a2^3*a3^4*b0^2*b3 + a1^3*a2^3*b3^5 + a1^3*a2*a3^6*b0^2*b1 +
   a1^3*a2*a3^2*b1*b3^4 + a1^2*a2^10*b0*b2 + a1^2*a2^9*a3*b0*b1 +
   a1^2*a2^8*a3^2*b0^2 + a1^2*a2^8*b0*b3^2 + a1^2*a2^8*b2^3 +
   a1^2*a2^7*a3*b1*b2^2 + a1^2*a2^6*a3^2*b0*b2^2 + a1^2*a2^6*a3^2*b1^2*b2 +
   a1^2*a2^6*b2^2*b3^2 + a1^2*a2^5*a3^3*b1^3 + a1^2*a2^4*a3^4*b0^2*b2 +
   a1^2*a2^4*a3^4*b0*b1^2 + a1^2*a2^4*a3^2*b1^2*b3^2 + a1^2*a2^4*b2*b3^4 +
   a1^2*a2^3*a3^5*b0^2*b1 + a1^2*a2^3*a3*b1*b3^4 + a1^2*a2^2*a3^6*b0^3 +
   a1^2*a2^2*a3^4*b0^2*b3^2 + a1^2*a2^2*a3^2*b0*b3^4 + a1^2*a2^2*b3^6 +
   a1*a2^11*b0*b1 + a1*a2^9*b1*b2^2 + a1*a2^7*a3^2*b1^3 +
   a1*a2^5*a3^4*b0^2*b1 + a1*a2^5*b1*b3^4 + a2^12*b0^2 + a2^8*b2^4 +
   a2^4*a3^4*b1^4 + a3^8*b0^4 + b3^8
   E = a0^10*a3^4*b6^3 + a0^9*a1*a3^4*b5*b6^2 + a0^9*a2*a3^4*b5^2*b6 +
   a0^9*a3^5*b3*b6^2 + a0^9*a3^5*b4*b5*b6 + a0^9*a3^5*b5^3 +
   a0^9*a3^3*b5^3*b6 + a0^8*a1^2*a3^4*b4*b6^2 + a0^8*a1*a2*a3^4*b3*b6^2 +
   a0^8*a1*a2*a3^4*b4*b5*b6 + a0^8*a1*a2*a3^2*b5^3*b6 +
   a0^8*a1*a3^5*b3*b5*b6 + a0^8*a1*a3^5*b4*b5^2 + a0^8*a1*a3^3*b5^4 +
   a0^8*a2^2*a3^4*b4^2*b6 + a0^8*a2^2*b5^4*b6 + a0^8*a2*a3^5*b1*b6^2 +
   a0^8*a2*a3^5*b2*b5*b6 + a0^8*a2*a3^5*b3*b4*b6 + a0^8*a2*a3^5*b4^2*b5 +
   a0^8*a2*a3^3*b3*b5^2*b6 + a0^8*a2*a3*b5^5 + a0^8*a3^6*b0*b6^2 +
   a0^8*a3^6*b1*b5*b6 + a0^8*a3^6*b2*b4*b6 + a0^8*a3^6*b2*b5^2 +
   a0^8*a3^6*b3^2*b6 + a0^8*a3^6*b3*b4*b5 + a0^8*a3^6*b4^3 +
   a0^8*a3^4*b2*b5^2*b6 + a0^8*a3^4*b3^2*b6^2 + a0^8*a3^4*b3*b5^3 +
   a0^8*a3^4*b4^2*b5^2 + a0^8*a3^2*b4*b5^4 + a0^8*b5^6 +
   a0^7*a1^3*a3^4*b3*b6^2 + a0^7*a1^2*a2^2*a3*b5^3*b6 +
   a0^7*a1^2*a2*a3^4*b3*b5*b6 + a0^7*a1^2*a2*a3^2*b5^4 +
   a0^7*a1^2*a3^5*b1*b6^2 + a0^7*a1^2*a3^5*b2*b5*b6 +
   a0^7*a1^2*a3^5*b3*b5^2 + a0^7*a1^2*a3^3*b4*b5^3 + a0^7*a1^2*a3*b5^5 +
   a0^7*a1*a2^2*a3^4*b1*b6^2 + a0^7*a1*a2^2*a3^4*b2*b5*b6 +
   a0^7*a1*a2^2*a3^4*b3*b4*b6 + a0^7*a1*a2^2*a3^2*b3*b5^2*b6 +
   a0^7*a1*a2*a3^5*b1*b5*b6 + a0^7*a1*a2*a3^5*b2*b5^2 +
   a0^7*a1*a2*a3^5*b3^2*b6 + a0^7*a1*a2*a3^5*b3*b4*b5 +
   a0^7*a1*a2*a3^3*b3*b5^3 + a0^7*a1*a3^6*b1*b4*b6 +
   a0^7*a1*a3^6*b2*b3*b6 + a0^7*a1*a3^6*b2*b4*b5 + a0^7*a1*a3^6*b3*b4^2 +
   a0^7*a1*a3^4*b1*b5^2*b6 + a0^7*a1*a3^4*b2*b5^3 + a0^7*a1*a3^2*b3*b5^4 +
   a0^7*a2^3*a3^4*b3^2*b6 + a0^7*a2^2*a3^5*b0*b5*b6 +
   a0^7*a2^2*a3^5*b1*b4*b6 + a0^7*a2^2*a3^5*b2*b3*b6 +
   a0^7*a2^2*a3^5*b3^2*b5 + a0^7*a2^2*a3^3*b1*b5^2*b6 +
   a0^7*a2^2*a3^3*b3^2*b5*b6 + a0^7*a2*a3^6*b0*b5^2 + a0^7*a2*a3^6*b1*b3*b6 +
   a0^7*a2*a3^6*b1*b4*b5 + a0^7*a2*a3^6*b2*b3*b5 + a0^7*a2*a3^6*b3^2*b4 +
   a0^7*a2*a3^4*b1*b5^3 + a0^7*a3^7*b0*b4*b5 + a0^7*a3^7*b1*b2*b6 +
   a0^7*a3^7*b1*b3*b5 + a0^7*a3^7*b1*b4^2 + a0^7*a3^7*b2^2*b5 +
   a0^7*a3^7*b2*b3*b4 + a0^7*a3^7*b3^3 + a0^7*a3^5*b0*b5^3 +
   a0^7*a3^5*b2*b3*b5^2 + a0^7*a3^5*b3^2*b4*b5 + a0^7*a3^3*b1*b5^4 +
   a0^7*a3^3*b3^2*b5^3 + a0^6*a1^4*a2^4*b6^3 + a0^6*a1^4*a3^4*b2*b6^2 +
   a0^6*a1^4*b5^4*b6 + a0^6*a1^3*a2^3*b5^3*b6 + a0^6*a1^3*a2^2*a3*b5^4 +
   a0^6*a1^3*a2*a3^4*b1*b6^2 + a0^6*a1^3*a2*a3^4*b2*b5*b6 +
   a0^6*a1^3*a2*a3^2*b4*b5^3 + a0^6*a1^3*a2*b5^5 + a0^6*a1^3*a3^5*b1*b5*b6 +
   a0^6*a1^3*a3^5*b2*b5^2 + a0^6*a1^3*a3^3*b3*b5^3 +
   a0^6*a1^2*a2^3*a3*b3*b5^2*b6 + a0^6*a1^2*a2^2*a3^4*b0*b6^2 +
   a0^6*a1^2*a2^2*a3^4*b2*b4*b6 + a0^6*a1^2*a2^2*a3^2*b3*b5^3 +
   a0^6*a1^2*a2*a3^5*b0*b5*b6 + a0^6*a1^2*a2*a3^5*b2*b3*b6 +
   a0^6*a1^2*a2*a3^5*b2*b4*b5 + a0^6*a1^2*a2*a3^3*b3*b4*b5^2 +
   a0^6*a1^2*a2*a3*b3*b5^4 + a0^6*a1^2*a3^6*b0*b4*b6 +
   a0^6*a1^2*a3^6*b0*b5^2 + a0^6*a1^2*a3^6*b1*b3*b6 +
   a0^6*a1^2*a3^6*b1*b4*b5 + a0^6*a1^2*a3^6*b2*b4^2 +
   a0^6*a1^2*a3^4*b0*b5^2*b6 + a0^6*a1^2*a3^4*b2*b4*b5^2 +
   a0^6*a1^2*a3^4*b3^2*b5^2 + a0^6*a1*a2^3*a3^4*b0*b5*b6 +
   a0^6*a1*a2^3*a3^4*b1*b4*b6 + a0^6*a1*a2^3*a3^4*b2*b3*b6 +
   a0^6*a1*a2^3*a3^2*b1*b5^2*b6 + a0^6*a1*a2^3*a3^2*b3^2*b5*b6 +
   a0^6*a1*a2^2*a3^5*b0*b5^2 + a0^6*a1*a2^2*a3^5*b1*b4*b5 +
   a0^6*a1*a2^2*a3^5*b2*b3*b5 + a0^6*a1*a2^2*a3^3*b1*b5^3 +
   a0^6*a1*a2^2*a3^3*b3^2*b5^2 + a0^6*a1*a2*a3^6*b0*b4*b5 +
   a0^6*a1*a2*a3^6*b1*b2*b6 + a0^6*a1*a2*a3^6*b1*b4^2 +
   a0^6*a1*a2*a3^6*b2^2*b5 + a0^6*a1*a2*a3^6*b2*b3*b4 +
   a0^6*a1*a2*a3^4*b0*b5^3 + a0^6*a1*a2*a3^4*b2*b3*b5^2 +
   a0^6*a1*a2*a3^4*b3^2*b4*b5 + a0^6*a1*a2*a3^2*b1*b5^4 +
   a0^6*a1*a2*a3^2*b3^2*b5^3 + a0^6*a1*a3^7*b0*b3*b5 +
   a0^6*a1*a3^7*b1^2*b6 + a0^6*a1*a3^7*b1*b2*b5 + a0^6*a1*a3^7*b1*b3*b4 +
   a0^6*a1*a3^7*b2*b3^2 + a0^6*a1*a3^5*b1*b3*b5^2 + a0^6*a1*a3^5*b3^3*b5 +
   a0^6*a2^4*a3^4*b2^2*b6 + a0^6*a2^3*a3^5*b0*b3*b6 +
   a0^6*a2^3*a3^5*b1*b2*b6 + a0^6*a2^3*a3^5*b2^2*b5 +
   a0^6*a2^3*a3^3*b3^3*b6 + a0^6*a2^2*a3^6*b0*b2*b6 +
   a0^6*a2^2*a3^6*b0*b3*b5 + a0^6*a2^2*a3^6*b1^2*b6 +
   a0^6*a2^2*a3^6*b1*b2*b5 + a0^6*a2^2*a3^6*b2^2*b4 +
   a0^6*a2^2*a3^4*b1^2*b6^2 + a0^6*a2^2*a3^4*b2^2*b5^2 +
   a0^6*a2^2*a3^4*b2*b3^2*b6 + a0^6*a2^2*a3^4*b3^3*b5 +
   a0^6*a2*a3^7*b0*b2*b5 + a0^6*a2*a3^7*b0*b3*b4 + a0^6*a2*a3^7*b1*b2*b4 +
   a0^6*a2*a3^7*b2^2*b3 + a0^6*a2*a3^5*b0*b3*b5^2 + a0^6*a2*a3^5*b1^2*b5*b6 +
   a0^6*a2*a3^5*b1*b2*b5^2 + a0^6*a2*a3^5*b2*b3^2*b5 + a0^6*a2*a3^5*b3^3*b4 +
   a0^6*a2*a3^3*b3^3*b5^2 + a0^6*a3^8*b0^2*b6 + a0^6*a3^8*b0*b1*b5 +
   a0^6*a3^8*b0*b2*b4 + a0^6*a3^8*b0*b3^2 + a0^6*a3^8*b1^2*b4 +
   a0^6*a3^8*b1*b2*b3 + a0^6*a3^8*b2^3 + a0^6*a3^6*b0*b2*b5^2 +
   a0^6*a3^6*b1^2*b4*b6 + a0^6*a3^6*b1*b3^2*b5 + a0^6*a3^6*b2*b3^2*b4 +
   a0^6*a3^6*b3^4 + a0^6*a3^4*b1^2*b5^2*b6 + a0^6*a3^4*b2*b3^2*b5^2 +
   a0^6*a3^4*b3^4*b6 + a0^5*a1^5*a2^4*b5*b6^2 + a0^5*a1^5*a3^4*b1*b6^2 +
   a0^5*a1^5*b5^5 + a0^5*a1^4*a2^5*b5^2*b6 + a0^5*a1^4*a2^4*a3*b3*b6^2 +
   a0^5*a1^4*a2^4*a3*b4*b5*b6 + a0^5*a1^4*a2^4*a3*b5^3 +
   a0^5*a1^4*a2^3*b5^4 + a0^5*a1^4*a2^2*a3*b4*b5^3 +
   a0^5*a1^4*a2*a3^4*b1*b5*b6 + a0^5*a1^4*a2*a3^2*b3*b5^3 +
   a0^5*a1^4*a3^5*b0*b5*b6 + a0^5*a1^4*a3^5*b1*b5^2 +
   a0^5*a1^4*a3^3*b2*b5^3 + a0^5*a1^4*a3*b3*b5^4 +
   a0^5*a1^3*a2^4*b3*b5^2*b6 + a0^5*a1^3*a2^3*a3*b3*b5^3 +
   a0^5*a1^3*a2^2*a3^4*b0*b5*b6 + a0^5*a1^3*a2^2*a3^4*b1*b4*b6 +
   a0^5*a1^3*a2^2*a3^2*b3*b4*b5^2 + a0^5*a1^3*a2^2*b3*b5^4 +
   a0^5*a1^3*a2*a3^5*b0*b5^2 + a0^5*a1^3*a2*a3^5*b1*b3*b6 +
   a0^5*a1^3*a2*a3^5*b1*b4*b5 + a0^5*a1^3*a2*a3^3*b3^2*b5^2 +
   a0^5*a1^3*a3^6*b0*b3*b6 + a0^5*a1^3*a3^6*b0*b4*b5 +
   a0^5*a1^3*a3^6*b1*b4^2 + a0^5*a1^3*a3^4*b0*b5^3 +
   a0^5*a1^3*a3^4*b1*b4*b5^2 + a0^5*a1^3*a3^4*b2*b3*b5^2 +
   a0^5*a1^2*a2^4*a3*b1*b5^2*b6 + a0^5*a1^2*a2^4*a3*b3^2*b5*b6 +
   a0^5*a1^2*a2^3*a3^4*b1*b3*b6 + a0^5*a1^2*a2^3*a3^2*b1*b5^3 +
   a0^5*a1^2*a2^3*a3^2*b3^2*b5^2 + a0^5*a1^2*a2^2*a3^5*b0*b3*b6 +
   a0^5*a1^2*a2^2*a3^5*b1*b3*b5 + a0^5*a1^2*a2^2*a3^3*b1*b4*b5^2 +
   a0^5*a1^2*a2^2*a3^3*b3^2*b4*b5 + a0^5*a1^2*a2^2*a3*b1*b5^4 +
   a0^5*a1^2*a2^2*a3*b3^2*b5^3 + a0^5*a1^2*a2*a3^6*b1^2*b6 +
   a0^5*a1^2*a2*a3^6*b1*b2*b5 + a0^5*a1^2*a2*a3^6*b1*b3*b4 +
   a0^5*a1^2*a2*a3^4*b3^3*b5 + a0^5*a1^2*a3^7*b0*b1*b6 +
   a0^5*a1^2*a3^7*b0*b2*b5 + a0^5*a1^2*a3^7*b0*b3*b4 +
   a0^5*a1^2*a3^7*b1*b3^2 + a0^5*a1^2*a3^5*b0*b3*b5^2 +
   a0^5*a1^2*a3^5*b1^2*b5*b6 + a0^5*a1^2*a3^5*b1*b2*b5^2 +
   a0^5*a1^2*a3^5*b2*b3^2*b5 + a0^5*a1*a2^4*a3^4*b0*b3*b6 +
   a0^5*a1*a2^4*a3^4*b1*b2*b6 + a0^5*a1*a2^4*a3^2*b3^3*b6 +
   a0^5*a1*a2^3*a3^5*b0*b3*b5 + a0^5*a1*a2^3*a3^5*b1^2*b6 +
   a0^5*a1*a2^3*a3^5*b1*b2*b5 + a0^5*a1*a2^3*a3^3*b3^3*b5 +
   a0^5*a1*a2^2*a3^6*b0*b1*b6 + a0^5*a1*a2^2*a3^6*b0*b3*b4 +
   a0^5*a1*a2^2*a3^6*b1*b2*b4 + a0^5*a1*a2^2*a3^4*b0*b3*b5^2 +
   a0^5*a1*a2^2*a3^4*b1^2*b5*b6 + a0^5*a1*a2^2*a3^4*b1*b2*b5^2 +
   a0^5*a1*a2^2*a3^4*b1*b3^2*b6 + a0^5*a1*a2^2*a3^4*b3^3*b4 +
   a0^5*a1*a2^2*a3^2*b3^3*b5^2 + a0^5*a1*a2*a3^7*b0*b1*b5 +
   a0^5*a1*a2*a3^7*b0*b3^2 + a0^5*a1*a2*a3^7*b1^2*b4 +
   a0^5*a1*a2*a3^7*b1*b2*b3 + a0^5*a1*a2*a3^5*b1*b3^2*b5 +
   a0^5*a1*a2*a3^5*b3^4 + a0^5*a1*a3^8*b0^2*b5 + a0^5*a1*a3^8*b0*b1*b4 +
   a0^5*a1*a3^8*b0*b2*b3 + a0^5*a1*a3^8*b1*b2^2 + a0^5*a1*a3^6*b0*b1*b5^2 +
   a0^5*a1*a3^6*b1^2*b3*b6 + a0^5*a1*a3^6*b1^2*b4*b5 +
   a0^5*a1*a3^6*b1*b3^2*b4 + a0^5*a1*a3^6*b2*b3^3 + a0^5*a1*a3^4*b1^2*b5^3 +
   a0^5*a1*a3^4*b1*b3^2*b5^2 + a0^5*a1*a3^4*b3^4*b5 +
   a0^5*a2^5*a3^4*b1^2*b6 + a0^5*a2^4*a3^5*b0*b1*b6 +
   a0^5*a2^4*a3^5*b1^2*b5 + a0^5*a2^4*a3^3*b1^2*b5*b6 +
   a0^5*a2^4*a3^3*b1*b3^2*b6 + a0^5*a2^3*a3^6*b0*b1*b5 +
   a0^5*a2^3*a3^6*b1^2*b4 + a0^5*a2^3*a3^4*b1*b3^2*b5 +
   a0^5*a2^2*a3^7*b0^2*b5 + a0^5*a2^2*a3^7*b0*b1*b4 +
   a0^5*a2^2*a3^7*b1^2*b3 + a0^5*a2^2*a3^5*b0*b1*b5^2 +
   a0^5*a2^2*a3^5*b1^2*b3*b6 + a0^5*a2^2*a3^5*b1^2*b4*b5 +
   a0^5*a2^2*a3^5*b1*b3^2*b4 + a0^5*a2^2*a3^3*b1^2*b5^3 +
   a0^5*a2^2*a3^3*b1*b3^2*b5^2 + a0^5*a2^2*a3^3*b3^4*b5 +
   a0^5*a2*a3^8*b0*b1*b3 + a0^5*a2*a3^8*b1^2*b2 + a0^5*a2*a3^6*b1^2*b3*b5 +
   a0^5*a2*a3^6*b1*b3^3 + a0^5*a3^9*b0^2*b3 + a0^5*a3^9*b0*b1*b2 +
   a0^5*a3^9*b1^3 + a0^5*a3^7*b1^3*b6 + a0^5*a3^7*b1^2*b3*b4 +
   a0^5*a3^7*b1*b2*b3^2 + a0^5*a3^5*b1^2*b3*b5^2 + a0^5*a3^5*b3^5 +
   a0^4*a1^6*a2^4*b4*b6^2 + a0^4*a1^6*a3^4*b0*b6^2 + a0^4*a1^6*b4*b5^4 +
   a0^4*a1^5*a2^5*b3*b6^2 + a0^4*a1^5*a2^5*b4*b5*b6 +
   a0^4*a1^5*a2^4*a3*b3*b5*b6 + a0^4*a1^5*a2^4*a3*b4*b5^2 +
   a0^4*a1^5*a2^3*b4*b5^3 + a0^4*a1^5*a2^2*a3*b3*b5^3 +
   a0^4*a1^5*a2*a3^4*b0*b5*b6 + a0^4*a1^5*a2*a3^2*b2*b5^3 +
   a0^4*a1^5*a2*b3*b5^4 + a0^4*a1^5*a3^5*b0*b5^2 +
   a0^4*a1^5*a3^3*b1*b5^3 + a0^4*a1^4*a2^6*b4^2*b6 +
   a0^4*a1^4*a2^5*a3*b1*b6^2 + a0^4*a1^4*a2^5*a3*b2*b5*b6 +
   a0^4*a1^4*a2^5*a3*b3*b4*b6 + a0^4*a1^4*a2^5*a3*b4^2*b5 +
   a0^4*a1^4*a2^4*a3^2*b0*b6^2 + a0^4*a1^4*a2^4*a3^2*b1*b5*b6 +
   a0^4*a1^4*a2^4*a3^2*b2*b4*b6 + a0^4*a1^4*a2^4*a3^2*b2*b5^2 +
   a0^4*a1^4*a2^4*a3^2*b3^2*b6 + a0^4*a1^4*a2^4*a3^2*b3*b4*b5 +
   a0^4*a1^4*a2^4*a3^2*b4^3 + a0^4*a1^4*a2^4*b2*b5^2*b6 +
   a0^4*a1^4*a2^4*b3^2*b6^2 + a0^4*a1^4*a2^4*b4^2*b5^2 +
   a0^4*a1^4*a2^3*a3*b3*b4*b5^2 + a0^4*a1^4*a2^2*a3^4*b0*b4*b6 +
   a0^4*a1^4*a2^2*a3^2*b3^2*b5^2 + a0^4*a1^4*a2^2*b2*b5^4 +
   a0^4*a1^4*a2*a3^5*b0*b3*b6 + a0^4*a1^4*a2*a3^5*b0*b4*b5 +
   a0^4*a1^4*a2*a3^3*b2*b3*b5^2 + a0^4*a1^4*a2*a3*b1*b5^4 +
   a0^4*a1^4*a3^6*b0*b4^2 + a0^4*a1^4*a3^4*b0*b4*b5^2 +
   a0^4*a1^4*a3^4*b1^2*b6^2 + a0^4*a1^4*a3^4*b1*b3*b5^2 +
   a0^4*a1^4*a3^2*b0*b5^4 + a0^4*a1^4*b3^2*b5^4 + a0^4*a1^3*a2^5*b1*b5^2*b6 +
   a0^4*a1^3*a2^5*b3^2*b5*b6 + a0^4*a1^3*a2^4*a3*b1*b5^3 +
   a0^4*a1^3*a2^4*a3*b3^2*b5^2 + a0^4*a1^3*a2^3*a3^4*b0*b3*b6 +
   a0^4*a1^3*a2^3*a3^2*b1*b4*b5^2 + a0^4*a1^3*a2^3*a3^2*b3^2*b4*b5 +
   a0^4*a1^3*a2^3*b1*b5^4 + a0^4*a1^3*a2^3*b3^2*b5^3 +
   a0^4*a1^3*a2^2*a3^5*b0*b3*b5 + a0^4*a1^3*a2^2*a3^3*b1*b3*b5^2 +
   a0^4*a1^3*a2^2*a3^3*b3^3*b5 + a0^4*a1^3*a2*a3^6*b0*b1*b6 +
   a0^4*a1^3*a2*a3^6*b0*b2*b5 + a0^4*a1^3*a2*a3^6*b0*b3*b4 +
   a0^4*a1^3*a2*a3^4*b0*b3*b5^2 + a0^4*a1^3*a2*a3^4*b1^2*b5*b6 +
   a0^4*a1^3*a2*a3^4*b1*b2*b5^2 + a0^4*a1^3*a2*a3^4*b2*b3^2*b5 +
   a0^4*a1^3*a3^7*b0*b3^2 + a0^4*a1^3*a3^5*b1*b3^2*b5 +
   a0^4*a1^2*a2^5*a3*b3^3*b6 + a0^4*a1^2*a2^4*a3^4*b0*b2*b6 +
   a0^4*a1^2*a2^4*a3^2*b3^3*b5 + a0^4*a1^2*a2^3*a3^5*b0*b1*b6 +
   a0^4*a1^2*a2^3*a3^5*b0*b2*b5 + a0^4*a1^2*a2^3*a3^3*b3^3*b4 +
   a0^4*a1^2*a2^3*a3*b3^3*b5^2 + a0^4*a1^2*a2^2*a3^6*b0^2*b6 +
   a0^4*a1^2*a2^2*a3^6*b0*b2*b4 + a0^4*a1^2*a2^2*a3^4*b0*b2*b5^2 +
   a0^4*a1^2*a2^2*a3^4*b0*b3^2*b6 + a0^4*a1^2*a2^2*a3^4*b1^2*b4*b6 +
   a0^4*a1^2*a2^2*a3^4*b3^4 + a0^4*a1^2*a2*a3^7*b0^2*b5 +
   a0^4*a1^2*a2*a3^7*b0*b1*b4 + a0^4*a1^2*a2*a3^7*b0*b2*b3 +
   a0^4*a1^2*a2*a3^5*b0*b1*b5^2 + a0^4*a1^2*a2*a3^5*b0*b3^2*b5 +
   a0^4*a1^2*a2*a3^5*b1^2*b3*b6 + a0^4*a1^2*a2*a3^5*b1^2*b4*b5 +
   a0^4*a1^2*a2*a3^5*b2*b3^3 + a0^4*a1^2*a3^8*b0*b2^2 +
   a0^4*a1^2*a3^6*b0^2*b5^2 + a0^4*a1^2*a3^6*b0*b3^2*b4 +
   a0^4*a1^2*a3^6*b1^2*b4^2 + a0^4*a1^2*a3^6*b1*b3^3 +
   a0^4*a1^2*a3^4*b0*b3^2*b5^2 + a0^4*a1^2*a3^4*b1^2*b4*b5^2 +
   a0^4*a1^2*a3^4*b3^4*b4 + a0^4*a1*a2^5*a3^4*b0*b1*b6 +
   a0^4*a1*a2^5*a3^2*b1^2*b5*b6 + a0^4*a1*a2^5*a3^2*b1*b3^2*b6 +
   a0^4*a1*a2^4*a3^5*b0*b1*b5 + a0^4*a1*a2^4*a3^3*b1^2*b5^2 +
   a0^4*a1*a2^4*a3^3*b1*b3^2*b5 + a0^4*a1*a2^3*a3^6*b0^2*b5 +
   a0^4*a1*a2^3*a3^6*b0*b1*b4 + a0^4*a1*a2^3*a3^4*b0*b1*b5^2 +
   a0^4*a1*a2^3*a3^4*b1^2*b3*b6 + a0^4*a1*a2^3*a3^4*b1^2*b4*b5 +
   a0^4*a1*a2^3*a3^4*b1*b3^2*b4 + a0^4*a1*a2^3*a3^2*b1^2*b5^3 +
   a0^4*a1*a2^3*a3^2*b1*b3^2*b5^2 + a0^4*a1*a2^3*a3^2*b3^4*b5 +
   a0^4*a1*a2^2*a3^7*b0*b1*b3 + a0^4*a1*a2^2*a3^5*b1*b3^3 +
   a0^4*a1*a2*a3^8*b0^2*b3 + a0^4*a1*a2*a3^8*b0*b1*b2 +
   a0^4*a1*a2*a3^6*b1^3*b6 + a0^4*a1*a2*a3^6*b1^2*b3*b4 +
   a0^4*a1*a2*a3^6*b1*b2*b3^2 + a0^4*a1*a2*a3^4*b1^2*b3*b5^2 +
   a0^4*a1*a2*a3^4*b3^5 + a0^4*a1*a3^9*b0*b1^2 + a0^4*a1*a3^7*b1^3*b5 +
   a0^4*a2^6*a3^4*b0^2*b6 + a0^4*a2^6*b3^4*b6 + a0^4*a2^5*a3^5*b0^2*b5 +
   a0^4*a2^5*a3^3*b1^2*b3*b6 + a0^4*a2^5*a3*b3^4*b5 +
   a0^4*a2^4*a3^6*b0^2*b4 + a0^4*a2^4*a3^4*b0^2*b5^2 +
   a0^4*a2^4*a3^4*b1^2*b2*b6 + a0^4*a2^4*a3^4*b1^2*b3*b5 +
   a0^4*a2^4*a3^2*b3^4*b4 + a0^4*a2^4*b3^4*b5^2 + a0^4*a2^3*a3^7*b0^2*b3 +
   a0^4*a2^3*a3^5*b1^3*b6 + a0^4*a2^3*a3^5*b1^2*b2*b5 +
   a0^4*a2^3*a3^5*b1^2*b3*b4 + a0^4*a2^3*a3^3*b1^2*b3*b5^2 +
   a0^4*a2^3*a3^3*b3^5 + a0^4*a2^2*a3^8*b0^2*b2 + a0^4*a2^2*a3^6*b0*b1^2*b6 +
   a0^4*a2^2*a3^6*b1^2*b2*b4 + a0^4*a2^2*a3^6*b1^2*b3^2 +
   a0^4*a2^2*a3^4*b1^2*b2*b5^2 + a0^4*a2^2*a3^4*b1^2*b3^2*b6 +
   a0^4*a2^2*a3^4*b2*b3^4 + a0^4*a2*a3^9*b0^2*b1 + a0^4*a2*a3^7*b0*b1^2*b5 +
   a0^4*a2*a3^7*b1^3*b4 + a0^4*a2*a3^5*b1^3*b5^2 +
   a0^4*a2*a3^5*b1^2*b3^2*b5 + a0^4*a2*a3^5*b1*b3^4 + a0^4*a3^10*b0^3 +
   a0^4*a3^8*b0^2*b3^2 + a0^4*a3^8*b0*b1^2*b4 + a0^4*a3^8*b1^3*b3 +
   a0^4*a3^8*b1^2*b2^2 + a0^4*a3^6*b0*b1^2*b5^2 + a0^4*a3^6*b0*b3^4 +
   a0^4*a3^6*b1^2*b3^2*b4 + a0^4*a3^4*b1^2*b3^2*b5^2 + a0^4*a3^4*b3^6 +
   a0^3*a1^7*a2^4*b3*b6^2 + a0^3*a1^7*b3*b5^4 + a0^3*a1^6*a2^5*b3*b5*b6 +
   a0^3*a1^6*a2^4*a3*b1*b6^2 + a0^3*a1^6*a2^4*a3*b2*b5*b6 +
   a0^3*a1^6*a2^4*a3*b3*b5^2 + a0^3*a1^6*a2^3*b3*b5^3 +
   a0^3*a1^6*a2^2*a3*b2*b5^3 + a0^3*a1^6*a2*a3^2*b1*b5^3 +
   a0^3*a1^6*a3^3*b0*b5^3 + a0^3*a1^6*a3*b1*b5^4 +
   a0^3*a1^5*a2^6*b1*b6^2 + a0^3*a1^5*a2^6*b2*b5*b6 +
   a0^3*a1^5*a2^6*b3*b4*b6 + a0^3*a1^5*a2^5*a3*b1*b5*b6 +
   a0^3*a1^5*a2^5*a3*b2*b5^2 + a0^3*a1^5*a2^5*a3*b3^2*b6 +
   a0^3*a1^5*a2^5*a3*b3*b4*b5 + a0^3*a1^5*a2^4*a3^2*b1*b4*b6 +
   a0^3*a1^5*a2^4*a3^2*b2*b3*b6 + a0^3*a1^5*a2^4*a3^2*b2*b4*b5 +
   a0^3*a1^5*a2^4*a3^2*b3*b4^2 + a0^3*a1^5*a2^4*b1*b5^2*b6 +
   a0^3*a1^5*a2^4*b2*b5^3 + a0^3*a1^5*a2^4*b3*b4*b5^2 +
   a0^3*a1^5*a2^3*a3*b3^2*b5^2 + a0^3*a1^5*a2^2*a3^2*b2*b3*b5^2 +
   a0^3*a1^5*a2*a3^3*b1*b3*b5^2 + a0^3*a1^5*a3^4*b0*b3*b5^2 +
   a0^3*a1^4*a2^7*b3^2*b6 + a0^3*a1^4*a2^6*a3*b0*b5*b6 +
   a0^3*a1^4*a2^6*a3*b1*b4*b6 + a0^3*a1^4*a2^6*a3*b2*b3*b6 +
   a0^3*a1^4*a2^6*a3*b3^2*b5 + a0^3*a1^4*a2^5*a3^2*b0*b5^2 +
   a0^3*a1^4*a2^5*a3^2*b1*b3*b6 + a0^3*a1^4*a2^5*a3^2*b1*b4*b5 +
   a0^3*a1^4*a2^5*a3^2*b2*b3*b5 + a0^3*a1^4*a2^5*a3^2*b3^2*b4 +
   a0^3*a1^4*a2^5*b3^2*b5^2 + a0^3*a1^4*a2^4*a3^3*b0*b4*b5 +
   a0^3*a1^4*a2^4*a3^3*b1*b2*b6 + a0^3*a1^4*a2^4*a3^3*b1*b3*b5 +
   a0^3*a1^4*a2^4*a3^3*b1*b4^2 + a0^3*a1^4*a2^4*a3^3*b2^2*b5 +
   a0^3*a1^4*a2^4*a3^3*b2*b3*b4 + a0^3*a1^4*a2^4*a3^3*b3^3 +
   a0^3*a1^4*a2^4*a3*b0*b5^3 + a0^3*a1^4*a2^4*a3*b1*b4*b5^2 +
   a0^3*a1^4*a2^4*a3*b2*b3*b5^2 + a0^3*a1^4*a2^3*a3^2*b1*b3*b5^2 +
   a0^3*a1^4*a2^3*a3^2*b3^3*b5 + a0^3*a1^4*a2^2*a3^3*b1*b2*b5^2 +
   a0^3*a1^4*a2^2*a3^3*b2*b3^2*b5 + a0^3*a1^4*a2*a3^4*b1^2*b5^2 +
   a0^3*a1^4*a2*a3^4*b1*b3^2*b5 + a0^3*a1^4*a3^5*b0*b1*b5^2 +
   a0^3*a1^4*a3^5*b0*b3^2*b5 + a0^3*a1^4*a3^3*b1^2*b5^3 +
   a0^3*a1^3*a2^6*b3^3*b6 + a0^3*a1^3*a2^5*a3*b3^3*b5 +
   a0^3*a1^3*a2^4*a3^2*b3^3*b4 + a0^3*a1^3*a2^4*b3^3*b5^2 +
   a0^3*a1^3*a2^3*a3^3*b3^4 + a0^3*a1^3*a2^2*a3^4*b2*b3^3 +
   a0^3*a1^3*a2*a3^5*b1*b3^3 + a0^3*a1^3*a3^6*b0*b3^3 +
   a0^3*a1^3*a3^4*b1^2*b3*b5^2 + a0^3*a1^3*a3^4*b3^5 +
   a0^3*a1^2*a2^6*a3*b1^2*b5*b6 + a0^3*a1^2*a2^6*a3*b1*b3^2*b6 +
   a0^3*a1^2*a2^5*a3^2*b1^2*b5^2 + a0^3*a1^2*a2^5*a3^2*b1*b3^2*b5 +
   a0^3*a1^2*a2^4*a3^3*b1^2*b4*b5 + a0^3*a1^2*a2^4*a3^3*b1*b3^2*b4 +
   a0^3*a1^2*a2^4*a3*b1^2*b5^3 + a0^3*a1^2*a2^4*a3*b1*b3^2*b5^2 +
   a0^3*a1^2*a2^3*a3^4*b1^2*b3*b5 + a0^3*a1^2*a2^3*a3^4*b1*b3^3 +
   a0^3*a1^2*a2^2*a3^5*b1^2*b2*b5 + a0^3*a1^2*a2^2*a3^5*b1*b2*b3^2 +
   a0^3*a1^2*a2*a3^6*b1^3*b5 + a0^3*a1^2*a2*a3^6*b1^2*b3^2 +
   a0^3*a1^2*a3^7*b0*b1^2*b5 + a0^3*a1^2*a3^7*b0*b1*b3^2 +
   a0^3*a1^2*a3^5*b1^3*b5^2 + a0^3*a1^2*a3^5*b1^2*b3^2*b5 +
   a0^3*a1^2*a3^5*b1*b3^4 + a0^3*a1*a2^6*a3^2*b1^2*b3*b6 +
   a0^3*a1*a2^5*a3^3*b1^2*b3*b5 + a0^3*a1*a2^4*a3^4*b1^2*b3*b4 +
   a0^3*a1*a2^4*a3^2*b1^2*b3*b5^2 + a0^3*a1*a2^3*a3^5*b1^2*b3^2 +
   a0^3*a1*a2^2*a3^6*b1^2*b2*b3 + a0^3*a1*a2*a3^7*b1^3*b3 +
   a0^3*a1*a3^8*b0*b1^2*b3 + a0^3*a1*a3^6*b1^2*b3^3 +
   a0^3*a2^6*a3^3*b1^3*b6 + a0^3*a2^5*a3^4*b1^3*b5 + a0^3*a2^4*a3^5*b1^3*b4 +
   a0^3*a2^4*a3^3*b1^3*b5^2 + a0^3*a2^3*a3^6*b1^3*b3 +
   a0^3*a2^2*a3^7*b1^3*b2 + a0^3*a2*a3^8*b1^4 + a0^3*a3^9*b0*b1^3 +
   a0^3*a3^7*b1^4*b5 + a0^3*a3^7*b1^3*b3^2 + a0^2*a1^8*a2^4*b2*b6^2 +
   a0^2*a1^8*b2*b5^4 + a0^2*a1^7*a2^5*b1*b6^2 + a0^2*a1^7*a2^5*b2*b5*b6 +
   a0^2*a1^7*a2^4*a3*b1*b5*b6 + a0^2*a1^7*a2^4*a3*b2*b5^2 +
   a0^2*a1^7*a2^3*b2*b5^3 + a0^2*a1^7*a2^2*a3*b1*b5^3 +
   a0^2*a1^7*a2*a3^2*b0*b5^3 + a0^2*a1^7*a2*b1*b5^4 +
   a0^2*a1^6*a2^6*b0*b6^2 + a0^2*a1^6*a2^6*b2*b4*b6 +
   a0^2*a1^6*a2^5*a3*b0*b5*b6 + a0^2*a1^6*a2^5*a3*b2*b3*b6 +
   a0^2*a1^6*a2^5*a3*b2*b4*b5 + a0^2*a1^6*a2^4*a3^2*b0*b4*b6 +
   a0^2*a1^6*a2^4*a3^2*b0*b5^2 + a0^2*a1^6*a2^4*a3^2*b1*b3*b6 +
   a0^2*a1^6*a2^4*a3^2*b1*b4*b5 + a0^2*a1^6*a2^4*a3^2*b2*b4^2 +
   a0^2*a1^6*a2^4*b0*b5^2*b6 + a0^2*a1^6*a2^4*b2*b4*b5^2 +
   a0^2*a1^6*a2^3*a3*b2*b3*b5^2 + a0^2*a1^6*a2^2*a3^2*b1*b3*b5^2 +
   a0^2*a1^6*a2*a3^3*b0*b3*b5^2 + a0^2*a1^5*a2^7*b0*b5*b6 +
   a0^2*a1^5*a2^7*b1*b4*b6 + a0^2*a1^5*a2^7*b2*b3*b6 +
   a0^2*a1^5*a2^6*a3*b0*b5^2 + a0^2*a1^5*a2^6*a3*b1*b4*b5 +
   a0^2*a1^5*a2^6*a3*b2*b3*b5 + a0^2*a1^5*a2^5*a3^2*b0*b4*b5 +
   a0^2*a1^5*a2^5*a3^2*b1*b2*b6 + a0^2*a1^5*a2^5*a3^2*b1*b4^2 +
   a0^2*a1^5*a2^5*a3^2*b2^2*b5 + a0^2*a1^5*a2^5*a3^2*b2*b3*b4 +
   a0^2*a1^5*a2^5*b0*b5^3 + a0^2*a1^5*a2^5*b1*b4*b5^2 +
   a0^2*a1^5*a2^5*b2*b3*b5^2 + a0^2*a1^5*a2^4*a3^3*b0*b3*b5 +
   a0^2*a1^5*a2^4*a3^3*b1^2*b6 + a0^2*a1^5*a2^4*a3^3*b1*b2*b5 +
   a0^2*a1^5*a2^4*a3^3*b1*b3*b4 + a0^2*a1^5*a2^4*a3^3*b2*b3^2 +
   a0^2*a1^5*a2^3*a3^2*b1*b2*b5^2 + a0^2*a1^5*a2^3*a3^2*b2*b3^2*b5 +
   a0^2*a1^5*a2^2*a3^3*b1^2*b5^2 + a0^2*a1^5*a2^2*a3^3*b1*b3^2*b5 +
   a0^2*a1^5*a2*a3^4*b0*b1*b5^2 + a0^2*a1^5*a2*a3^4*b0*b3^2*b5 +
   a0^2*a1^5*a2*a3^2*b1^2*b5^3 + a0^2*a1^4*a2^8*b2^2*b6 +
   a0^2*a1^4*a2^7*a3*b0*b3*b6 + a0^2*a1^4*a2^7*a3*b1*b2*b6 +
   a0^2*a1^4*a2^7*a3*b2^2*b5 + a0^2*a1^4*a2^6*a3^2*b0*b2*b6 +
   a0^2*a1^4*a2^6*a3^2*b0*b3*b5 + a0^2*a1^4*a2^6*a3^2*b1^2*b6 +
   a0^2*a1^4*a2^6*a3^2*b1*b2*b5 + a0^2*a1^4*a2^6*a3^2*b2^2*b4 +
   a0^2*a1^4*a2^6*b1^2*b6^2 + a0^2*a1^4*a2^6*b2^2*b5^2 +
   a0^2*a1^4*a2^6*b2*b3^2*b6 + a0^2*a1^4*a2^5*a3^3*b0*b2*b5 +
   a0^2*a1^4*a2^5*a3^3*b0*b3*b4 + a0^2*a1^4*a2^5*a3^3*b1*b2*b4 +
   a0^2*a1^4*a2^5*a3^3*b2^2*b3 + a0^2*a1^4*a2^5*a3*b0*b3*b5^2 +
   a0^2*a1^4*a2^5*a3*b1^2*b5*b6 + a0^2*a1^4*a2^5*a3*b1*b2*b5^2 +
   a0^2*a1^4*a2^5*a3*b2*b3^2*b5 + a0^2*a1^4*a2^4*a3^4*b0^2*b6 +
   a0^2*a1^4*a2^4*a3^4*b0*b1*b5 + a0^2*a1^4*a2^4*a3^4*b0*b2*b4 +
   a0^2*a1^4*a2^4*a3^4*b0*b3^2 + a0^2*a1^4*a2^4*a3^4*b1^2*b4 +
   a0^2*a1^4*a2^4*a3^4*b1*b2*b3 + a0^2*a1^4*a2^4*a3^4*b2^3 +
   a0^2*a1^4*a2^4*a3^2*b0*b2*b5^2 + a0^2*a1^4*a2^4*a3^2*b1^2*b4*b6 +
   a0^2*a1^4*a2^4*a3^2*b1*b3^2*b5 + a0^2*a1^4*a2^4*a3^2*b2*b3^2*b4 +
   a0^2*a1^4*a2^4*b1^2*b5^2*b6 + a0^2*a1^4*a2^4*b2*b3^2*b5^2 +
   a0^2*a1^4*a2^3*a3^3*b2*b3^3 + a0^2*a1^4*a2^2*a3^4*b1*b3^3 +
   a0^2*a1^4*a2*a3^5*b0*b3^3 + a0^2*a1^4*a2*a3^3*b1^2*b3*b5^2 +
   a0^2*a1^4*a3^4*b2*b3^4 + a0^2*a1^3*a2^7*b1^2*b5*b6 +
   a0^2*a1^3*a2^7*b1*b3^2*b6 + a0^2*a1^3*a2^6*a3*b1^2*b5^2 +
   a0^2*a1^3*a2^6*a3*b1*b3^2*b5 + a0^2*a1^3*a2^5*a3^2*b1^2*b4*b5 +
   a0^2*a1^3*a2^5*a3^2*b1*b3^2*b4 + a0^2*a1^3*a2^5*b1^2*b5^3 +
   a0^2*a1^3*a2^5*b1*b3^2*b5^2 + a0^2*a1^3*a2^4*a3^3*b1^2*b3*b5 +
   a0^2*a1^3*a2^4*a3^3*b1*b3^3 + a0^2*a1^3*a2^3*a3^4*b1^2*b2*b5 +
   a0^2*a1^3*a2^3*a3^4*b1*b2*b3^2 + a0^2*a1^3*a2^2*a3^5*b1^3*b5 +
   a0^2*a1^3*a2^2*a3^5*b1^2*b3^2 + a0^2*a1^3*a2*a3^6*b0*b1^2*b5 +
   a0^2*a1^3*a2*a3^6*b0*b1*b3^2 + a0^2*a1^3*a2*a3^4*b1^3*b5^2 +
   a0^2*a1^3*a2*a3^4*b1^2*b3^2*b5 + a0^2*a1^3*a2*a3^4*b1*b3^4 +
   a0^2*a1^2*a2^7*a3*b1^2*b3*b6 + a0^2*a1^2*a2^6*a3^2*b1^2*b3*b5 +
   a0^2*a1^2*a2^5*a3^3*b1^2*b3*b4 + a0^2*a1^2*a2^5*a3*b1^2*b3*b5^2 +
   a0^2*a1^2*a2^4*a3^4*b1^2*b3^2 + a0^2*a1^2*a2^3*a3^5*b1^2*b2*b3 +
   a0^2*a1^2*a2^2*a3^6*b1^3*b3 + a0^2*a1^2*a2*a3^7*b0*b1^2*b3 +
   a0^2*a1^2*a2*a3^5*b1^2*b3^3 + a0^2*a1*a2^7*a3^2*b1^3*b6 +
   a0^2*a1*a2^6*a3^3*b1^3*b5 + a0^2*a1*a2^5*a3^4*b1^3*b4 +
   a0^2*a1*a2^5*a3^2*b1^3*b5^2 + a0^2*a1*a2^4*a3^5*b1^3*b3 +
   a0^2*a1*a2^3*a3^6*b1^3*b2 + a0^2*a1*a2^2*a3^7*b1^4 +
   a0^2*a1*a2*a3^8*b0*b1^3 + a0^2*a1*a2*a3^6*b1^4*b5 +
   a0^2*a1*a2*a3^6*b1^3*b3^2 + a0^2*a2^4*a3^4*b1^4*b6 +
   a0^2*a2*a3^7*b1^4*b3 + a0^2*a3^8*b1^4*b2 + a0*a1^9*a2^4*b1*b6^2 +
   a0*a1^9*b1*b5^4 + a0*a1^8*a2^5*b1*b5*b6 + a0*a1^8*a2^4*a3*b0*b5*b6 +
   a0*a1^8*a2^4*a3*b1*b5^2 + a0*a1^8*a2^3*b1*b5^3 +
   a0*a1^8*a2^2*a3*b0*b5^3 + a0*a1^7*a2^6*b0*b5*b6 +
   a0*a1^7*a2^6*b1*b4*b6 + a0*a1^7*a2^5*a3*b0*b5^2 +
   a0*a1^7*a2^5*a3*b1*b3*b6 + a0*a1^7*a2^5*a3*b1*b4*b5 +
   a0*a1^7*a2^4*a3^2*b0*b3*b6 + a0*a1^7*a2^4*a3^2*b0*b4*b5 +
   a0*a1^7*a2^4*a3^2*b1*b4^2 + a0*a1^7*a2^4*b0*b5^3 +
   a0*a1^7*a2^4*b1*b4*b5^2 + a0*a1^7*a2^3*a3*b1*b3*b5^2 +
   a0*a1^7*a2^2*a3^2*b0*b3*b5^2 + a0*a1^6*a2^7*b1*b3*b6 +
   a0*a1^6*a2^6*a3*b0*b3*b6 + a0*a1^6*a2^6*a3*b1*b3*b5 +
   a0*a1^6*a2^5*a3^2*b1^2*b6 + a0*a1^6*a2^5*a3^2*b1*b2*b5 +
   a0*a1^6*a2^5*a3^2*b1*b3*b4 + a0*a1^6*a2^5*b1*b3*b5^2 +
   a0*a1^6*a2^4*a3^3*b0*b1*b6 + a0*a1^6*a2^4*a3^3*b0*b2*b5 +
   a0*a1^6*a2^4*a3^3*b0*b3*b4 + a0*a1^6*a2^4*a3^3*b1*b3^2 +
   a0*a1^6*a2^4*a3*b0*b3*b5^2 + a0*a1^6*a2^4*a3*b1^2*b5*b6 +
   a0*a1^6*a2^3*a3^2*b1^2*b5^2 + a0*a1^6*a2^3*a3^2*b1*b3^2*b5 +
   a0*a1^6*a2^2*a3^3*b0*b1*b5^2 + a0*a1^6*a2^2*a3^3*b0*b3^2*b5 +
   a0*a1^6*a2^2*a3*b1^2*b5^3 + a0*a1^5*a2^8*b0*b3*b6 +
   a0*a1^5*a2^8*b1*b2*b6 + a0*a1^5*a2^7*a3*b0*b3*b5 +
   a0*a1^5*a2^7*a3*b1^2*b6 + a0*a1^5*a2^7*a3*b1*b2*b5 +
   a0*a1^5*a2^6*a3^2*b0*b1*b6 + a0*a1^5*a2^6*a3^2*b0*b3*b4 +
   a0*a1^5*a2^6*a3^2*b1*b2*b4 + a0*a1^5*a2^6*b0*b3*b5^2 +
   a0*a1^5*a2^6*b1^2*b5*b6 + a0*a1^5*a2^6*b1*b2*b5^2 +
   a0*a1^5*a2^6*b1*b3^2*b6 + a0*a1^5*a2^5*a3^3*b0*b1*b5 +
   a0*a1^5*a2^5*a3^3*b0*b3^2 + a0*a1^5*a2^5*a3^3*b1^2*b4 +
   a0*a1^5*a2^5*a3^3*b1*b2*b3 + a0*a1^5*a2^5*a3*b1*b3^2*b5 +
   a0*a1^5*a2^4*a3^4*b0^2*b5 + a0*a1^5*a2^4*a3^4*b0*b1*b4 +
   a0*a1^5*a2^4*a3^4*b0*b2*b3 + a0*a1^5*a2^4*a3^4*b1*b2^2 +
   a0*a1^5*a2^4*a3^2*b0*b1*b5^2 + a0*a1^5*a2^4*a3^2*b1^2*b3*b6 +
   a0*a1^5*a2^4*a3^2*b1^2*b4*b5 + a0*a1^5*a2^4*a3^2*b1*b3^2*b4 +
   a0*a1^5*a2^4*b1^2*b5^3 + a0*a1^5*a2^4*b1*b3^2*b5^2 +
   a0*a1^5*a2^3*a3^3*b1*b3^3 + a0*a1^5*a2^2*a3^4*b0*b3^3 +
   a0*a1^5*a2^2*a3^2*b1^2*b3*b5^2 + a0*a1^5*a3^4*b1*b3^4 +
   a0*a1^4*a2^9*b1^2*b6 + a0*a1^4*a2^8*a3*b0*b1*b6 +
   a0*a1^4*a2^8*a3*b1^2*b5 + a0*a1^4*a2^7*a3^2*b0*b1*b5 +
   a0*a1^4*a2^7*a3^2*b1^2*b4 + a0*a1^4*a2^7*b1^2*b5^2 +
   a0*a1^4*a2^6*a3^3*b0^2*b5 + a0*a1^4*a2^6*a3^3*b0*b1*b4 +
   a0*a1^4*a2^6*a3^3*b1^2*b3 + a0*a1^4*a2^6*a3*b0*b1*b5^2 +
   a0*a1^4*a2^6*a3*b1^2*b3*b6 + a0*a1^4*a2^5*a3^4*b0*b1*b3 +
   a0*a1^4*a2^5*a3^4*b1^2*b2 + a0*a1^4*a2^4*a3^5*b0^2*b3 +
   a0*a1^4*a2^4*a3^5*b0*b1*b2 + a0*a1^4*a2^4*a3^5*b1^3 +
   a0*a1^4*a2^4*a3^3*b1^3*b6 + a0*a1^4*a2^4*a3^3*b1^2*b2*b5 +
   a0*a1^4*a2^4*a3^3*b1^2*b3*b4 + a0*a1^4*a2^4*a3*b1^2*b3*b5^2 +
   a0*a1^4*a2^3*a3^4*b1^3*b5 + a0*a1^4*a2^3*a3^4*b1^2*b3^2 +
   a0*a1^4*a2^2*a3^5*b0*b1^2*b5 + a0*a1^4*a2^2*a3^5*b0*b1*b3^2 +
   a0*a1^4*a2^2*a3^3*b1^3*b5^2 + a0*a1^4*a2^2*a3^3*b1^2*b3^2*b5 +
   a0*a1^3*a2^8*b1^2*b3*b6 + a0*a1^3*a2^7*a3*b1^2*b3*b5 +
   a0*a1^3*a2^6*a3^2*b1^2*b3*b4 + a0*a1^3*a2^6*b1^2*b3*b5^2 +
   a0*a1^3*a2^5*a3^3*b1^2*b3^2 + a0*a1^3*a2^4*a3^4*b1^2*b2*b3 +
   a0*a1^3*a2^3*a3^5*b1^3*b3 + a0*a1^3*a2^2*a3^6*b0*b1^2*b3 +
   a0*a1^3*a2^2*a3^4*b1^2*b3^3 + a0*a1^2*a2^8*a3*b1^3*b6 +
   a0*a1^2*a2^7*a3^2*b1^3*b5 + a0*a1^2*a2^6*a3^3*b1^3*b4 +
   a0*a1^2*a2^6*a3*b1^3*b5^2 + a0*a1^2*a2^5*a3^4*b1^3*b3 +
   a0*a1^2*a2^4*a3^5*b1^3*b2 + a0*a1^2*a2^3*a3^6*b1^4 +
   a0*a1^2*a2^2*a3^7*b0*b1^3 + a0*a1^2*a2^2*a3^5*b1^4*b5 +
   a0*a1^2*a2^2*a3^5*b1^3*b3^2 + a0*a1*a2^4*a3^4*b1^4*b5 +
   a0*a1*a2^2*a3^6*b1^4*b3 + a0*a1*a3^8*b1^5 + a0*a2^6*a3^3*b1^4*b5 +
   a0*a2^4*a3^5*b1^4*b3 + a0*a2^2*a3^7*b1^5 + a1^10*a2^4*b0*b6^2 +
   a1^10*b0*b5^4 + a1^9*a2^5*b0*b5*b6 + a1^9*a2^4*a3*b0*b5^2 +
   a1^9*a2^3*b0*b5^3 + a1^8*a2^6*b0*b4*b6 + a1^8*a2^5*a3*b0*b3*b6 +
   a1^8*a2^5*a3*b0*b4*b5 + a1^8*a2^4*a3^2*b0*b4^2 + a1^8*a2^4*b0*b4*b5^2 +
   a1^8*a2^4*b1^2*b6^2 + a1^8*a2^3*a3*b0*b3*b5^2 + a1^8*b1^2*b5^4 +
   a1^7*a2^7*b0*b3*b6 + a1^7*a2^6*a3*b0*b3*b5 + a1^7*a2^5*a3^2*b0*b1*b6 +
   a1^7*a2^5*a3^2*b0*b2*b5 + a1^7*a2^5*a3^2*b0*b3*b4 + a1^7*a2^5*b0*b3*b5^2 +
   a1^7*a2^5*b1^2*b5*b6 + a1^7*a2^4*a3^3*b0*b3^2 + a1^7*a2^4*a3*b1^2*b5^2 +
   a1^7*a2^3*a3^2*b0*b1*b5^2 + a1^7*a2^3*a3^2*b0*b3^2*b5 +
   a1^7*a2^3*b1^2*b5^3 + a1^6*a2^8*b0*b2*b6 + a1^6*a2^7*a3*b0*b1*b6 +
   a1^6*a2^7*a3*b0*b2*b5 + a1^6*a2^6*a3^2*b0^2*b6 +
   a1^6*a2^6*a3^2*b0*b2*b4 + a1^6*a2^6*b0*b2*b5^2 + a1^6*a2^6*b0*b3^2*b6 +
   a1^6*a2^6*b1^2*b4*b6 + a1^6*a2^5*a3^3*b0^2*b5 + a1^6*a2^5*a3^3*b0*b1*b4 +
   a1^6*a2^5*a3^3*b0*b2*b3 + a1^6*a2^5*a3*b0*b1*b5^2 +
   a1^6*a2^5*a3*b0*b3^2*b5 + a1^6*a2^5*a3*b1^2*b3*b6 +
   a1^6*a2^5*a3*b1^2*b4*b5 + a1^6*a2^4*a3^4*b0*b2^2 +
   a1^6*a2^4*a3^2*b0^2*b5^2 + a1^6*a2^4*a3^2*b0*b3^2*b4 +
   a1^6*a2^4*a3^2*b1^2*b4^2 + a1^6*a2^4*b0*b3^2*b5^2 +
   a1^6*a2^4*b1^2*b4*b5^2 + a1^6*a2^3*a3^3*b0*b3^3 +
   a1^6*a2^3*a3*b1^2*b3*b5^2 + a1^6*a3^4*b0*b3^4 + a1^5*a2^9*b0*b1*b6 +
   a1^5*a2^8*a3*b0*b1*b5 + a1^5*a2^7*a3^2*b0^2*b5 + a1^5*a2^7*a3^2*b0*b1*b4 +
   a1^5*a2^7*b0*b1*b5^2 + a1^5*a2^7*b1^2*b3*b6 + a1^5*a2^6*a3^3*b0*b1*b3 +
   a1^5*a2^6*a3*b1^2*b3*b5 + a1^5*a2^5*a3^4*b0^2*b3 +
   a1^5*a2^5*a3^4*b0*b1*b2 + a1^5*a2^5*a3^2*b1^3*b6 +
   a1^5*a2^5*a3^2*b1^2*b2*b5 + a1^5*a2^5*a3^2*b1^2*b3*b4 +
   a1^5*a2^5*b1^2*b3*b5^2 + a1^5*a2^4*a3^5*b0*b1^2 +
   a1^5*a2^4*a3^3*b1^2*b3^2 + a1^5*a2^3*a3^4*b0*b1^2*b5 +
   a1^5*a2^3*a3^4*b0*b1*b3^2 + a1^5*a2^3*a3^2*b1^3*b5^2 +
   a1^5*a2^3*a3^2*b1^2*b3^2*b5 + a1^4*a2^10*b0^2*b6 + a1^4*a2^9*a3*b0^2*b5 +
   a1^4*a2^8*a3^2*b0^2*b4 + a1^4*a2^8*b0^2*b5^2 + a1^4*a2^8*b1^2*b2*b6 +
   a1^4*a2^7*a3^3*b0^2*b3 + a1^4*a2^7*a3*b1^3*b6 + a1^4*a2^7*a3*b1^2*b2*b5 +
   a1^4*a2^6*a3^4*b0^2*b2 + a1^4*a2^6*a3^2*b0*b1^2*b6 +
   a1^4*a2^6*a3^2*b1^2*b2*b4 + a1^4*a2^6*b1^2*b2*b5^2 +
   a1^4*a2^6*b1^2*b3^2*b6 + a1^4*a2^5*a3^5*b0^2*b1 +
   a1^4*a2^5*a3^3*b0*b1^2*b5 + a1^4*a2^5*a3^3*b1^3*b4 +
   a1^4*a2^5*a3^3*b1^2*b2*b3 + a1^4*a2^5*a3*b1^3*b5^2 +
   a1^4*a2^5*a3*b1^2*b3^2*b5 + a1^4*a2^4*a3^6*b0^3 +
   a1^4*a2^4*a3^4*b0^2*b3^2 + a1^4*a2^4*a3^4*b0*b1^2*b4 +
   a1^4*a2^4*a3^4*b1^2*b2^2 + a1^4*a2^4*a3^2*b0*b1^2*b5^2 +
   a1^4*a2^4*a3^2*b1^2*b3^2*b4 + a1^4*a2^4*b1^2*b3^2*b5^2 +
   a1^4*a2^3*a3^5*b0*b1^2*b3 + a1^4*a2^3*a3^3*b1^2*b3^3 +
   a1^4*a3^4*b1^2*b3^4 + a1^3*a2^9*b1^3*b6 + a1^3*a2^8*a3*b1^3*b5 +
   a1^3*a2^7*a3^2*b1^3*b4 + a1^3*a2^7*b1^3*b5^2 + a1^3*a2^6*a3^3*b1^3*b3 +
   a1^3*a2^5*a3^4*b1^3*b2 + a1^3*a2^4*a3^5*b1^4 + a1^3*a2^3*a3^6*b0*b1^3 +
   a1^3*a2^3*a3^4*b1^4*b5 + a1^3*a2^3*a3^4*b1^3*b3^2 +
   a1^2*a2^4*a3^4*b1^4*b4 + a1^2*a2^3*a3^5*b1^4*b3 + a1^2*a3^8*b0*b1^4 +
   a1*a2^7*a3^2*b1^4*b5 + a1*a2^5*a3^4*b1^4*b3 + a1*a2^3*a3^6*b1^5 +
   a2^10*b1^4*b6 + a2^9*a3*b1^4*b5 + a2^8*a3^2*b1^4*b4 + a2^8*b1^4*b5^2 +
   a2^7*a3^3*b1^4*b3 + a2^6*a3^4*b1^4*b2 + a2^5*a3^5*b1^5 +
   a2^4*a3^6*b0*b1^4 + a2^4*a3^4*b1^4*b3^2 + a3^8*b1^6
    return [A, B, C, D, E]
  end
  
  f = f + h^2//4
  
  if !(characteristic(K) in [2,3,5])
    a, b, c, d = igusa_clebsch_invariants(f)
    J2  = a//8
    J4  = (4*J2^2 - b)//96
    J6  = (8*J2^3 - 160*J2*J4 - c)//576
    J8  = (J2*J6 - J4^2)//4
    J10 = d//4096

  return [J2, J4, J6, J8, J10]
  end
  a0, a1, a2, a3, a4, a5, a6 = collect(coefficients(f))
  A = -480*a0*a6 + 80*a1*a5 - 32*a2*a4 + 12*a3^2
  B = 5280*a0^2*a6^2 - 1760*a0*a1*a5*a6 + 2624*a0*a2*a4*a6 - 800*a0*a2*a5^2
   - 1344*a0*a3^2*a6 + 480*a0*a3*a4*a5 - 128*a0*a4^3 - 800*a1^2*a4*a6 
   + 480*a1^2*a5^2 + 480*a1*a2*a3*a6 - 224*a1*a2*a4*a5 - 16*a1*a3^2*a5
   + 32*a1*a3*a4^2 - 128*a2^3*a6 + 32*a2^2*a3*a5 + 32*a2^2*a4^2 - 
   32*a2*a3^2*a4 + 6*a3^4
  C = 20480*a0^3*a6^3 - 10240*a0^2*a1*a5*a6^2 - 57344*a0^2*a2*a4*a6^2 
   + 25600*a0^2*a2*a5^2*a6 - 10176*a0^2*a3^2*a6^2 + 42240*a0^2*a3*a4*a5*a6
   - 16000*a0^2*a3*a5^3 - 16384*a0^2*a4^3*a6 + 6400*a0^2*a4^2*a5^2 
   + 25600*a0*a1^2*a4*a6^2 - 8960*a0*a1^2*a5^2*a6 + 42240*a0*a1*a2*a3*a6^2
   - 26112*a0*a1*a2*a4*a5*a6 + 6400*a0*a1*a2*a5^3 - 17728*a0*a1*a3^2*a5*a6
   + 10496*a0*a1*a3*a4^2*a6 + 2560*a0*a1*a3*a4*a5^2 - 1536*a0*a1*a4^3*a5 
   - 16384*a0*a2^3*a6^2 + 10496*a0*a2^2*a3*a5*a6 + 4096*a0*a2^2*a4^2*a6 
   - 2560*a0*a2^2*a4*a5^2 - 6272*a0*a2*a3^2*a4*a6 + 320*a0*a2*a3^2*a5^2 
   + 768*a0*a2*a3*a4^2*a5 + 1248*a0*a3^4*a6 - 192*a0*a3^3*a4*a5 
   - 16000*a1^3*a3*a6^2 + 6400*a1^3*a4*a5*a6 - 1280*a1^3*a5^3 
   + 6400*a1^2*a2^2*a6^2 + 2560*a1^2*a2*a3*a5*a6 - 2560*a1^2*a2*a4^2*a6 
   + 256*a1^2*a2*a4*a5^2 + 320*a1^2*a3^2*a4*a6 + 704*a1^2*a3^2*a5^2 
   - 896*a1^2*a3*a4^2*a5 + 256*a1^2*a4^4 - 1536*a1*a2^3*a5*a6 
   + 768*a1*a2^2*a3*a4*a6 - 896*a1*a2^2*a3*a5^2 + 512*a1*a2^2*a4^2*a5 
   - 192*a1*a2*a3^3*a6 + 448*a1*a2*a3^2*a4*a5 - 256*a1*a2*a3*a4^3 
   - 112*a1*a3^4*a5 + 64*a1*a3^3*a4^2 + 256*a2^4*a5^2 - 256*a2^3*a3*a4*a5 
   + 64*a2^2*a3^3*a5 + 64*a2^2*a3^2*a4^2 - 32*a2*a3^4*a4 + 4*a3^6
  D =  -9427200*a0^4*a6^4 + 6284800*a0^3*a1*a5*a6^3 - 209920*a0^3*a2*a4*a6^3 -
   960000*a0^3*a2*a5^2*a6^2 + 4830720*a0^3*a3^2*a6^3 -
   6336000*a0^3*a3*a4*a5*a6^2 + 1920000*a0^3*a3*a5^3*a6 +
   2304000*a0^3*a4^3*a6^2 - 768000*a0^3*a4^2*a5^2*a6 -
   960000*a0^2*a1^2*a4*a6^3 - 1171200*a0^2*a1^2*a5^2*a6^2 -
   6336000*a0^2*a1*a2*a3*a6^3 + 4968960*a0^2*a1*a2*a4*a5*a6^2 -
   960000*a0^2*a1*a2*a5^3*a6 + 752640*a0^2*a1*a3^2*a5*a6^2 -
   1344000*a0^2*a1*a3*a4^2*a6^2 + 960000*a0^2*a1*a3*a4*a5^2*a6 -
   320000*a0^2*a1*a3*a5^4 - 256000*a0^2*a1*a4^3*a5*a6 +
   128000*a0^2*a1*a4^2*a5^3 + 2304000*a0^2*a2^3*a6^3 -
   1344000*a0^2*a2^2*a3*a5*a6^2 - 1838592*a0^2*a2^2*a4^2*a6^2 +
   1152000*a0^2*a2^2*a4*a5^2*a6 - 160000*a0^2*a2^2*a5^4 +
   2509824*a0^2*a2*a3^2*a4*a6^2 - 499200*a0^2*a2*a3^2*a5^2*a6 -
   1059840*a0^2*a2*a3*a4^2*a5*a6 + 320000*a0^2*a2*a3*a4*a5^3 +
   299008*a0^2*a2*a4^4*a6 - 102400*a0^2*a2*a4^3*a5^2 -
   647712*a0^2*a3^4*a6^2 + 472320*a0^2*a3^3*a4*a5*a6 -
   48000*a0^2*a3^3*a5^3 - 135168*a0^2*a3^2*a4^3*a6 -
   38400*a0^2*a3^2*a4^2*a5^2 + 30720*a0^2*a3*a4^4*a5 - 
  4096*a0^2*a4^6 + 1920000*a0*a1^3*a3*a6^3 - 960000*a0*a1^3*a4*a5*a6^2 +
   396800*a0*a1^3*a5^3*a6 - 768000*a0*a1^2*a2^2*a6^3 +
   960000*a0*a1^2*a2*a3*a5*a6^2 + 1152000*a0*a1^2*a2*a4^2*a6^2 -
   1628160*a0*a1^2*a2*a4*a5^2*a6 + 320000*a0*a1^2*a2*a5^4 -
   499200*a0*a1^2*a3^2*a4*a6^2 - 157440*a0*a1^2*a3^2*a5^2*a6 +
   537600*a0*a1^2*a3*a4^2*a5*a6 - 64000*a0*a1^2*a3*a4*a5^3 -
   81920*a0*a1^2*a4^4*a6 - 256000*a0*a1*a2^3*a5*a6^2 -
   1059840*a0*a1*a2^2*a3*a4*a6^2 + 537600*a0*a1*a2^2*a3*a5^2*a6 +
   551424*a0*a1*a2^2*a4^2*a5*a6 - 192000*a0*a1*a2^2*a4*a5^3 +
   472320*a0*a1*a2*a3^3*a6^2 - 388608*a0*a1*a2*a3^2*a4*a5*a6 +
   19200*a0*a1*a2*a3^2*a5^3 - 64512*a0*a1*a2*a3*a4^3*a6 +
   61440*a0*a1*a2*a3*a4^2*a5^2 - 2048*a0*a1*a2*a4^4*a5 -
   20256*a0*a1*a3^4*a5*a6 + 45312*a0*a1*a3^3*a4^2*a6 +
   7680*a0*a1*a3^3*a4*a5^2 - 13312*a0*a1*a3^2*a4^3*a5 +
   2048*a0*a1*a3*a4^5 + 299008*a0*a2^4*a4*a6^2 - 81920*a0*a2^4*a5^2*a6 -
   135168*a0*a2^3*a3^2*a6^2 - 64512*a0*a2^3*a3*a4*a5*a6 +
   12800*a0*a2^3*a3*a5^3 - 82944*a0*a2^3*a4^3*a6 + 33280*a0*a2^3*a4^2*a5^2 +
   45312*a0*a2^2*a3^3*a5*a6 + 118272*a0*a2^2*a3^2*a4^2*a6 -
   30720*a0*a2^2*a3^2*a4*a5^2 - 11776*a0*a2^2*a3*a4^3*a5 +
   2048*a0*a2^2*a4^5 - 54336*a0*a2*a3^4*a4*a6 + 3360*a0*a2*a3^4*a5^2 +
   11520*a0*a2*a3^3*a4^2*a5 - 2048*a0*a2*a3^2*a4^4 + 7296*a0*a3^6*a6 -
   2016*a0*a3^5*a4*a5 + 384*a0*a3^4*a4^3 - 320000*a1^4*a3*a5*a6^2 -
   160000*a1^4*a4^2*a6^2 + 320000*a1^4*a4*a5^2*a6 - 83200*a1^4*a5^4 +
   128000*a1^3*a2^2*a5*a6^2 + 320000*a1^3*a2*a3*a4*a6^2 -
   64000*a1^3*a2*a3*a5^2*a6 - 192000*a1^3*a2*a4^2*a5*a6 +
   69120*a1^3*a2*a4*a5^3 - 48000*a1^3*a3^3*a6^2 + 19200*a1^3*a3^2*a4*a5*a6 +
   14080*a1^3*a3^2*a5^3 + 12800*a1^3*a3*a4^3*a6 - 25600*a1^3*a3*a4^2*a5^2 +
   5120*a1^3*a4^4*a5 - 102400*a1^2*a2^3*a4*a6^2 -
   38400*a1^2*a2^2*a3^2*a6^2 + 61440*a1^2*a2^2*a3*a4*a5*a6 -
   25600*a1^2*a2^2*a3*a5^3 + 33280*a1^2*a2^2*a4^3*a6 -
   12032*a1^2*a2^2*a4^2*a5^2 + 7680*a1^2*a2*a3^3*a5*a6 -
   30720*a1^2*a2*a3^2*a4^2*a6 + 9984*a1^2*a2*a3^2*a4*a5^2 +
   5632*a1^2*a2*a3*a4^3*a5 - 2048*a1^2*a2*a4^5 + 3360*a1^2*a3^4*a4*a6 -
   1632*a1^2*a3^4*a5^2 - 1152*a1^2*a3^3*a4^2*a5 + 512*a1^2*a3^2*a4^4 +
   30720*a1*a2^4*a3*a6^2 - 2048*a1*a2^4*a4*a5*a6 + 5120*a1*a2^4*a5^3 -
   13312*a1*a2^3*a3^2*a5*a6 - 11776*a1*a2^3*a3*a4^2*a6 +
   5632*a1*a2^3*a3*a4*a5^2 - 512*a1*a2^3*a4^3*a5 +
   11520*a1*a2^2*a3^3*a4*a6 - 1152*a1*a2^2*a3^3*a5^2 -
   4608*a1*a2^2*a3^2*a4^2*a5 + 1536*a1*a2^2*a3*a4^4 - 2016*a1*a2*a3^5*a6 +
   2016*a1*a2*a3^4*a4*a5 - 768*a1*a2*a3^3*a4^3 - 208*a1*a3^6*a5 +
   96*a1*a3^5*a4^2 - 4096*a2^6*a6^2 + 2048*a2^5*a3*a5*a6 +
   2048*a2^5*a4^2*a6 - 2048*a2^5*a4*a5^2 - 2048*a2^4*a3^2*a4*a6 +
   512*a2^4*a3^2*a5^2 + 1536*a2^4*a3*a4^2*a5 - 256*a2^4*a4^4 +
   384*a2^3*a3^4*a6 - 768*a2^3*a3^3*a4*a5 + 96*a2^2*a3^5*a5 +
   96*a2^2*a3^4*a4^2 - 32*a2*a3^6*a4 + 3*a3^8
   E = -11943936*a0^5*a6^5 + 9953280*a0^4*a1*a5*a6^4 + 15925248*a0^4*a2*a4*a6^4 -
   8294400*a0^4*a2*a5^2*a6^3 + 8957952*a0^4*a3^2*a6^4 -
   19906560*a0^4*a3*a4*a5*a6^3 + 6912000*a0^4*a3*a5^3*a6^2 -
   3538944*a0^4*a4^3*a6^3 + 11059200*a0^4*a4^2*a5^2*a6^2 -
   5760000*a0^4*a4*a5^4*a6 + 800000*a0^4*a5^6 - 8294400*a0^3*a1^2*a4*a6^4 +
   138240*a0^3*a1^2*a5^2*a6^3 - 19906560*a0^3*a1*a2*a3*a6^4 +
   8183808*a0^3*a1*a2*a4*a5*a6^3 - 460800*a0^3*a1*a2*a5^3*a6^2 +
   3981312*a0^3*a1*a3^2*a5*a6^3 + 11943936*a0^3*a1*a3*a4^2*a6^3 -
   8017920*a0^3*a1*a3*a4*a5^2*a6^2 + 576000*a0^3*a1*a3*a5^4*a6 -
   5603328*a0^3*a1*a4^3*a5*a6^2 + 3993600*a0^3*a1*a4^2*a5^3*a6 -
   640000*a0^3*a1*a4*a5^5 - 3538944*a0^3*a2^3*a6^4 +
   11943936*a0^3*a2^2*a3*a5*a6^3 - 4423680*a0^3*a2^2*a4^2*a6^3 -
   1658880*a0^3*a2^2*a4*a5^2*a6^2 + 384000*a0^3*a2^2*a5^4*a6 +
   995328*a0^3*a2*a3^2*a4*a6^3 - 7050240*a0^3*a2*a3^2*a5^2*a6^2 -
   884736*a0^3*a2*a3*a4^2*a5*a6^2 + 5068800*a0^3*a2*a3*a4*a5^3*a6 -
   960000*a0^3*a2*a3*a5^5 + 2359296*a0^3*a2*a4^4*a6^2 -
   2703360*a0^3*a2*a4^3*a5^2*a6 + 512000*a0^3*a2*a4^2*a5^4 -
   2239488*a0^3*a3^4*a6^3 + 5474304*a0^3*a3^3*a4*a5*a6^2 -
   345600*a0^3*a3^3*a5^3*a6 - 2211840*a0^3*a3^2*a4^3*a6^2 -
   2488320*a0^3*a3^2*a4^2*a5^2*a6 + 576000*a0^3*a3^2*a4*a5^4 +
   1769472*a0^3*a3*a4^4*a5*a6 - 409600*a0^3*a3*a4^3*a5^3 -
   262144*a0^3*a4^6*a6 + 65536*a0^3*a4^5*a5^2 + 6912000*a0^2*a1^3*a3*a6^4 -
   460800*a0^2*a1^3*a4*a5*a6^3 + 104960*a0^2*a1^3*a5^3*a6^2 +
   11059200*a0^2*a1^2*a2^2*a6^4 - 8017920*a0^2*a1^2*a2*a3*a5*a6^3 -
   1658880*a0^2*a1^2*a2*a4^2*a6^3 + 2239488*a0^2*a1^2*a2*a4*a5^2*a6^2 -
   435200*a0^2*a1^2*a2*a5^4*a6 - 7050240*a0^2*a1^2*a3^2*a4*a6^3 +
   3946752*a0^2*a1^2*a3^2*a5^2*a6^2 + 4257792*a0^2*a1^2*a3*a4^2*a5*a6^2 -
   3156480*a0^2*a1^2*a3*a4*a5^3*a6 + 512000*a0^2*a1^2*a3*a5^5 -
   49152*a0^2*a1^2*a4^4*a6^2 + 63488*a0^2*a1^2*a4^3*a5^2*a6 -
   12800*a0^2*a1^2*a4^2*a5^4 - 5603328*a0^2*a1*a2^3*a5*a6^3 -
   884736*a0^2*a1*a2^2*a3*a4*a6^3 + 4257792*a0^2*a1*a2^2*a3*a5^2*a6^2 +
   3907584*a0^2*a1*a2^2*a4^2*a5*a6^2 - 3338240*a0^2*a1*a2^2*a4*a5^3*a6 +
   576000*a0^2*a1*a2^2*a5^5 + 5474304*a0^2*a1*a2*a3^3*a6^3 -
   5861376*a0^2*a1*a2*a3^2*a4*a5*a6^2 + 506880*a0^2*a1*a2*a3^2*a5^3*a6 -
   1474560*a0^2*a1*a2*a3*a4^3*a6^2 + 2598912*a0^2*a1*a2*a3*a4^2*a5^2*a6 -
   524800*a0^2*a1*a2*a3*a4*a5^4 - 163840*a0^2*a1*a2*a4^4*a5*a6 +
   40960*a0^2*a1*a2*a4^3*a5^3 - 1617408*a0^2*a1*a3^4*a5*a6^2 +
   1492992*a0^2*a1*a3^3*a4^2*a6^2 + 1009152*a0^2*a1*a3^3*a4*a5^2*a6 -
   230400*a0^2*a1*a3^3*a5^4 - 1142784*a0^2*a1*a3^2*a4^3*a5*a6 +
   261120*a0^2*a1*a3^2*a4^2*a5^3 + 196608*a0^2*a1*a3*a4^5*a6 -
   49152*a0^2*a1*a3*a4^4*a5^2 + 2359296*a0^2*a2^4*a4*a6^3 -
   49152*a0^2*a2^4*a5^2*a6^2 - 2211840*a0^2*a2^3*a3^2*a6^3 -
   1474560*a0^2*a2^3*a3*a4*a5*a6^2 - 30720*a0^2*a2^3*a3*a5^3*a6 -
   1114112*a0^2*a2^3*a4^3*a6^2 + 1232896*a0^2*a2^3*a4^2*a5^2*a6 -
   230400*a0^2*a2^3*a4*a5^4 + 1492992*a0^2*a2^2*a3^3*a5*a6^2 +
   2101248*a0^2*a2^2*a3^2*a4^2*a6^2 - 1161216*a0^2*a2^2*a3^2*a4*a5^2*a6 +
   211200*a0^2*a2^2*a3^2*a5^4 - 638976*a0^2*a2^2*a3*a4^3*a5*a6 +
   143360*a0^2*a2^2*a3*a4^2*a5^3 + 131072*a0^2*a2^2*a4^5*a6 -
   32768*a0^2*a2^2*a4^4*a5^2 - 1244160*a0^2*a2*a3^4*a4*a6^2 +
   41472*a0^2*a2*a3^4*a5^2*a6 + 718848*a0^2*a2*a3^3*a4^2*a5*a6 -
   161280*a0^2*a2*a3^3*a4*a5^3 - 147456*a0^2*a2*a3^2*a4^4*a6 +
   36864*a0^2*a2*a3^2*a4^3*a5^2 + 186624*a0^2*a3^6*a6^2 -
   124416*a0^2*a3^5*a4*a5*a6 + 27648*a0^2*a3^5*a5^3 +
   27648*a0^2*a3^4*a4^3*a6 - 6912*a0^2*a3^4*a4^2*a5^2 -
   5760000*a0*a1^4*a2*a6^4 + 576000*a0*a1^4*a3*a5*a6^3 +
   384000*a0*a1^4*a4^2*a6^3 - 435200*a0*a1^4*a4*a5^2*a6^2 +
   81920*a0*a1^4*a5^4*a6 + 3993600*a0*a1^3*a2^2*a5*a6^3 +
   5068800*a0*a1^3*a2*a3*a4*a6^3 - 3156480*a0*a1^3*a2*a3*a5^2*a6^2 -
   3338240*a0*a1^3*a2*a4^2*a5*a6^2 + 2500608*a0*a1^3*a2*a4*a5^3*a6 -
   409600*a0*a1^3*a2*a5^5 - 345600*a0*a1^3*a3^3*a6^3 +
   506880*a0*a1^3*a3^2*a4*a5*a6^2 - 53248*a0*a1^3*a3^2*a5^3*a6 -
   30720*a0*a1^3*a3*a4^3*a6^2 - 174592*a0*a1^3*a3*a4^2*a5^2*a6 +
   40960*a0*a1^3*a3*a4*a5^4 + 36864*a0*a1^3*a4^4*a5*a6 -
   9216*a0*a1^3*a4^3*a5^3 - 2703360*a0*a1^2*a2^3*a4*a6^3 +
   63488*a0*a1^2*a2^3*a5^2*a6^2 - 2488320*a0*a1^2*a2^2*a3^2*a6^3 +
   2598912*a0*a1^2*a2^2*a3*a4*a5*a6^2 - 174592*a0*a1^2*a2^2*a3*a5^3*a6 +
   1232896*a0*a1^2*a2^2*a4^3*a6^2 - 1389568*a0*a1^2*a2^2*a4^2*a5^2*a6 +
   261120*a0*a1^2*a2^2*a4*a5^4 + 1009152*a0*a1^2*a2*a3^3*a5*a6^2 -
   1161216*a0*a1^2*a2*a3^2*a4^2*a6^2 - 617472*a0*a1^2*a2*a3^2*a4*a5^2*a6 +
   143360*a0*a1^2*a2*a3^2*a5^4 + 837632*a0*a1^2*a2*a3*a4^3*a5*a6 -
   190976*a0*a1^2*a2*a3*a4^2*a5^3 - 147456*a0*a1^2*a2*a4^5*a6 +
   36864*a0*a1^2*a2*a4^4*a5^2 + 41472*a0*a1^2*a3^4*a4*a6^2 -
   27648*a0*a1^2*a3^3*a4^2*a5*a6 + 6144*a0*a1^2*a3^3*a4*a5^3 +
   6144*a0*a1^2*a3^2*a4^4*a6 - 1536*a0*a1^2*a3^2*a4^3*a5^2 +
   1769472*a0*a1*a2^4*a3*a6^3 - 163840*a0*a1*a2^4*a4*a5*a6^2 +
   36864*a0*a1*a2^4*a5^3*a6 - 1142784*a0*a1*a2^3*a3^2*a5*a6^2 -
   638976*a0*a1*a2^3*a3*a4^2*a6^2 + 837632*a0*a1*a2^3*a3*a4*a5^2*a6 -
   161280*a0*a1*a2^3*a3*a5^4 - 24576*a0*a1*a2^3*a4^3*a5*a6 +
   6144*a0*a1*a2^3*a4^2*a5^3 + 718848*a0*a1*a2^2*a3^3*a4*a6^2 -
   27648*a0*a1*a2^2*a3^3*a5^2*a6 - 405504*a0*a1*a2^2*a3^2*a4^2*a5*a6 +
   91136*a0*a1*a2^2*a3^2*a4*a5^3 + 81920*a0*a1*a2^2*a3*a4^4*a6 -
   20480*a0*a1*a2^2*a3*a4^3*a5^2 - 124416*a0*a1*a2*a3^5*a6^2 +
   82944*a0*a1*a2*a3^4*a4*a5*a6 - 18432*a0*a1*a2*a3^4*a5^3 -
   18432*a0*a1*a2*a3^3*a4^3*a6 + 4608*a0*a1*a2*a3^3*a4^2*a5^2 -
   262144*a0*a2^6*a6^3 + 196608*a0*a2^5*a3*a5*a6^2 +
   131072*a0*a2^5*a4^2*a6^2 - 147456*a0*a2^5*a4*a5^2*a6 +
   27648*a0*a2^5*a5^4 - 147456*a0*a2^4*a3^2*a4*a6^2 +
   6144*a0*a2^4*a3^2*a5^2*a6 + 81920*a0*a2^4*a3*a4^2*a5*a6 -
   18432*a0*a2^4*a3*a4*a5^3 - 16384*a0*a2^4*a4^4*a6 +
   4096*a0*a2^4*a4^3*a5^2 + 27648*a0*a2^3*a3^4*a6^2 -
   18432*a0*a2^3*a3^3*a4*a5*a6 + 4096*a0*a2^3*a3^3*a5^3 +
   4096*a0*a2^3*a3^2*a4^3*a6 - 1024*a0*a2^3*a3^2*a4^2*a5^2 +
   800000*a1^6*a6^4 - 640000*a1^5*a2*a5*a6^3 - 960000*a1^5*a3*a4*a6^3 +
   512000*a1^5*a3*a5^2*a6^2 + 576000*a1^5*a4^2*a5*a6^2 -
   409600*a1^5*a4*a5^3*a6 + 65536*a1^5*a5^5 + 512000*a1^4*a2^2*a4*a6^3 -
   12800*a1^4*a2^2*a5^2*a6^2 + 576000*a1^4*a2*a3^2*a6^3 -
   524800*a1^4*a2*a3*a4*a5*a6^2 + 40960*a1^4*a2*a3*a5^3*a6 -
   230400*a1^4*a2*a4^3*a6^2 + 261120*a1^4*a2*a4^2*a5^2*a6 -
   49152*a1^4*a2*a4*a5^4 - 230400*a1^4*a3^3*a5*a6^2 +
   211200*a1^4*a3^2*a4^2*a6^2 + 143360*a1^4*a3^2*a4*a5^2*a6 -
   32768*a1^4*a3^2*a5^4 - 161280*a1^4*a3*a4^3*a5*a6 +
   36864*a1^4*a3*a4^2*a5^3 + 27648*a1^4*a4^5*a6 -
   6912*a1^4*a4^4*a5^2 - 409600*a1^3*a2^3*a3*a6^3 +
   40960*a1^3*a2^3*a4*a5*a6^2 - 9216*a1^3*a2^3*a5^3*a6 +
   261120*a1^3*a2^2*a3^2*a5*a6^2 + 143360*a1^3*a2^2*a3*a4^2*a6^2 -
   190976*a1^3*a2^2*a3*a4*a5^2*a6 + 36864*a1^3*a2^2*a3*a5^4 +
   6144*a1^3*a2^2*a4^3*a5*a6 - 1536*a1^3*a2^2*a4^2*a5^3 -
   161280*a1^3*a2*a3^3*a4*a6^2 + 6144*a1^3*a2*a3^3*a5^2*a6 +
   91136*a1^3*a2*a3^2*a4^2*a5*a6 - 20480*a1^3*a2*a3^2*a4*a5^3 -
   18432*a1^3*a2*a3*a4^4*a6 + 4608*a1^3*a2*a3*a4^3*a5^2 +
   27648*a1^3*a3^5*a6^2 - 18432*a1^3*a3^4*a4*a5*a6 + 4096*a1^3*a3^4*a5^3 +
   4096*a1^3*a3^3*a4^3*a6 - 1024*a1^3*a3^3*a4^2*a5^2 +
   65536*a1^2*a2^5*a6^3 - 49152*a1^2*a2^4*a3*a5*a6^2 -
   32768*a1^2*a2^4*a4^2*a6^2 + 36864*a1^2*a2^4*a4*a5^2*a6 -
   6912*a1^2*a2^4*a5^4 + 36864*a1^2*a2^3*a3^2*a4*a6^2 -
   1536*a1^2*a2^3*a3^2*a5^2*a6 - 20480*a1^2*a2^3*a3*a4^2*a5*a6 +
   4608*a1^2*a2^3*a3*a4*a5^3 + 4096*a1^2*a2^3*a4^4*a6 -
   1024*a1^2*a2^3*a4^3*a5^2 - 6912*a1^2*a2^2*a3^4*a6^2 +
   4608*a1^2*a2^2*a3^3*a4*a5*a6 - 1024*a1^2*a2^2*a3^3*a5^3 -
   1024*a1^2*a2^2*a3^2*a4^3*a6 + 256*a1^2*a2^2*a3^2*a4^2*a5^2

  return [divexact(A, 2^4), divexact(B, 2^8), divexact(C, 2^12), divexact(D, 2^16), divexact(E, 2^20)] 
end



function clebsch_invariants(C::HypellCrv)
  f, h = hyperelliptic_polynomials(C)
  return clebsch_invariants(f + h^2/4)
end 

function igusa_invariants(C::HypellCrv)
  f, h = hyperelliptic_polynomials(C)
  return igusa_invariants(f, h)
end 

function igusa_clebsch_invariants(C::HypellCrv)
  f, h = hyperelliptic_polynomials(C)
  return igusa_clebsch_invariants(f + h^2/4)
end 

################################################################################
#
#  String I/O
#
################################################################################

function show(io::IO, C::HypellCrv)
  f, h = hyperelliptic_polynomials(C)
  #Swapped order of x and y to get nicer printing
  g = genus(C)
  if !is_zero(h)
    print(io, "Hyperelliptic curve of genus $(g) with equation\n y^2 + ($(h))*y = $(f)")
  else
    print(io, "Hyperelliptic curve of genus $(g) with equation\n y^2 = $(f)")
  end
end

function show(io::IO, P::HypellCrvPt)
   print(io, "Point  ($(P[1]) : $(P[2]) : $(P[3]))  of $(P.parent)")
end

@doc raw"""
    ==(P::EllipticCurvePoint, Q::EllipticCurvePoint) -> Bool

Return true if $P$ and $Q$ are equal and live over the same hyperelliptic curve
$E$.
"""
function ==(P::HypellCrvPt{T}, Q::HypellCrvPt{T}) where T
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

function Base.hash(P::HypellCrvPt, h::UInt)
  h = hash(parent(P), h)
  h = hash(P[1], h)
  h = hash(P[2], h)
  h = hash(P[3], h)
  return h
end
