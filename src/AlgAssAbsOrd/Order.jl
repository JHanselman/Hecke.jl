elem_type(::Type{AlgAssAbsOrd{S, T}}) where {S, T} = AlgAssAbsOrdElem{S, T}

ideal_type(::AlgAssAbsOrd{S, T}) where {S, T} = AlgAssAbsOrdIdl{S, T}

ideal_type(::Type{AlgAssAbsOrd{S, T}}) where {S, T} = AlgAssAbsOrdIdl{S, T}

# There is no dedicated type for fractional ideals
fractional_ideal_type(::AlgAssAbsOrd{S, T}) where {S, T} = AlgAssAbsOrdIdl{S, T}

fractional_ideal_type(::Type{AlgAssAbsOrd{S, T}}) where {S, T} = AlgAssAbsOrdIdl{S, T}

@doc raw"""
    algebra(O::AlgAssAbsOrd) -> AbstractAssociativeAlgebra

Returns the algebra which contains $O$.
"""
algebra(O::AlgAssAbsOrd) = O.algebra

_algebra(O::AlgAssAbsOrd) = algebra(O)

base_ring(O::AlgAssAbsOrd) = ZZ

base_ring_type(::Type{AlgAssAbsOrd}) = ZZRing

@doc raw"""
    is_commutative(O::AlgAssAbsOrd) -> Bool

Returns `true` if $O$ is a commutative ring and `false` otherwise.
"""
is_commutative(O::AlgAssAbsOrd) = is_commutative(algebra(O))

is_maximal_known(O::AlgAssAbsOrd) = O.is_maximal != 0

@inline is_maximal_known_and_maximal(O::AlgAssAbsOrd) = isone(O.is_maximal)

@doc raw"""
    is_maximal(O::AlgAssAbsOrd) -> Bool

Returns `true` if $O$ is a maximal order and `false` otherwise.
"""
function is_maximal(O::AlgAssAbsOrd)
  if O.is_maximal == 1
    return true
  end
  if O.is_maximal == 2
    return false
  end

  A = algebra(O)
  d = discriminant(O)
  if isdefined(A, :maximal_order)
    if d == discriminant(maximal_order(A))
      O.is_maximal = 1
      return true
    else
      O.is_maximal = 2
      return false
    end
  end

  if typeof(A) <: GroupAlgebra
    fac = factor(degree(O))
  else
    fac = factor(abs(d))
  end

  for (p, j) in fac
    # This can be improved a bit. Even in the GroupAlgebra case, we should
    # only look at the primes dividing d with power > 1
    if !(typeof(A) <: GroupAlgebra) && j == 1
      continue
    end
    d2 = discriminant(pmaximal_overorder(O, p))
    if d != d2
      O.is_maximal = 2
      return false
    end
  end
  O.is_maximal = 1
  return true
end

################################################################################
#
#  Construction
#
################################################################################

@doc raw"""
    Order(A::AbstractAssociativeAlgebra{QQFieldElem}, B::Vector{<: AbstractAssociativeAlgebraElem{QQFieldElem}}; check::Bool = true,
          isbasis::Bool = false, cached::Bool = true)
      -> AlgAssAbsOrd

Returns the order of $A$ generated by $B$. If `check` is set, it is checked
whether $B$ defines an order. If `isbasis` is set, then the elements are
assumed to form a $\mathbb Z$-basis.
"""
function Order(A::S, B::Vector{T}; check::Bool = true, isbasis::Bool = false, cached::Bool = true) where {S <: AbstractAssociativeAlgebra{QQFieldElem}, T <: AbstractAssociativeAlgebraElem{QQFieldElem}}
  if isbasis
    if check
      b, bmat, bmat_inv, _ = defines_order(A, B)
      if !b
        error("The elements do not define an order")
      else
        return AlgAssAbsOrd{S, elem_type(S)}(A, bmat, bmat_inv, deepcopy(B), cached)
      end
    else
      return AlgAssAbsOrd{S, elem_type(S)}(A, deepcopy(B), cached)
    end
  else
    return _order(A, B; cached = cached, check = check)
  end
end

@doc raw"""
    Order(A::AbstractAssociativeAlgebra{QQFieldElem}, M::FakeFmpqMat; check::Bool = true,
          cached::Bool = true)
      -> AlgAssAbsOrd

Returns the order of $A$ with basis matrix $M$. If `check` is set, it is checked
whether $M$ defines an order.
"""
function Order(A::S, M::FakeFmpqMat; check::Bool = true, cached::Bool = true) where {S <: AbstractAssociativeAlgebra{QQFieldElem}}
  if check
    b, Minv, v = defines_order(A, M)
    if !b
      error("The basis matrix does not define an order")
    else
      return AlgAssAbsOrd{S, elem_type(S)}(A, deepcopy(M), Minv, v, cached)
    end
  else
    return AlgAssAbsOrd{S, elem_type(S)}(A, deepcopy(M), cached)
  end
end

function _equation_order(A::AbstractAssociativeAlgebra{QQFieldElem})
  @assert is_commutative(A)
  a = primitive_element_via_number_fields(A)
  b = Vector{elem_type(A)}(undef, dim(A))
  b[1] = one(A)
  for i = 2:dim(A)
    b[i] = b[i - 1]*a
  end
  return Order(A, b)
end

################################################################################
#
#  Integral group ring
#
################################################################################

function integral_group_ring(A::GroupAlgebra{QQFieldElem})
  return Order(A, basis(A))
end

################################################################################
#
#  Index
#
################################################################################

function _det_basis_matrix(O::AlgAssAbsOrd)
  if isdefined(O, :det_basis_matrix)
    return O.det_basis_matrix
  else
    d = det(basis_matrix(FakeFmpqMat, O, copy = false))
    O.det_basis_matrix = d
    return d
  end
end

function index(O::AlgAssAbsOrd)
  B = basis_mat_inv(FakeFmpqMat, O, copy = false)
  n = det(B)
  @assert isinteger(n)
  return ZZ(n)
end

function index(O::AlgAssAbsOrd, R::AlgAssAbsOrd)
  B = basis_mat_inv(FakeFmpqMat, O, copy = false)
  n = det(B)
  B = basis_mat_inv(FakeFmpqMat, R, copy = false)
  m = det(B)
  @assert isinteger(m//n)
  return ZZ(m//n)
end

################################################################################
#
#  "Assure" functions for fields
#
################################################################################

function _assure_has_basis(O::AlgAssAbsOrd)
  if !isdefined(O, :basis)
    B = basis(algebra(O))
    M = basis_matrix(FakeFmpqMat, O, copy = false)
    v = Vector{elem_type(O)}(undef, degree(O))
    for i in 1:degree(O)
      w = sum(M.num[i, j]//M.den * B[j] for j in 1:degree(O))
      v[i] = O(w)
    end
    O.basis = v
  end
  return nothing
end

function assure_basis_mat_inv(O::AlgAssAbsOrd)
  if !isdefined(O, :basis_mat_inv)
    O.basis_mat_inv = inv(basis_matrix(FakeFmpqMat, O, copy = false))
  end
  return nothing
end

function assure_basis_alg(O::AlgAssAbsOrd)
  if isdefined(O, :basis_alg)
    return nothing
  end

  M = basis_matrix(FakeFmpqMat, O, copy = false)
  A = algebra(O)
  O.basis_alg = Vector{elem_type(A)}(undef, dim(A))
  for i = 1:dim(A)
    O.basis_alg[i] = elem_from_mat_row(A, M.num, i, M.den)
  end
  return nothing
end

################################################################################
#
#  Basis
#
################################################################################

@doc raw"""
    basis(O::AlgAssAbsOrd; copy::Bool = true) -> Vector{AlgAssAbsOrdElem}

Returns a $\mathbb Z$-basis of $O$.
"""
function basis(O::AlgAssAbsOrd; copy::Bool = true)
  _assure_has_basis(O)
  if copy
    return deepcopy(O.basis)::Vector{elem_type(O)}
  else
    return O.basis::Vector{elem_type(O)}
  end
end

absolute_basis(O::AlgAssAbsOrd) = basis(O)

function basis_alg(O::AlgAssAbsOrd{S, T}; copy::Bool = true) where {S, T}
  assure_basis_alg(O)
  if copy
    return deepcopy(O.basis_alg)::Vector{T}
  else
    return O.basis_alg::Vector{T}
  end
end

function basis(O::AlgAssAbsOrd{S, T}, A::S; copy::Bool = true) where {S, T}
  @req algebra(O) === A "Algebras do not match"
  return basis_alg(O, copy = copy)
end

################################################################################
#
#  (Inverse) basis matrix
#
################################################################################

@doc raw"""
    basis_matrix(O::AlgAssAbsOrd; copy::Bool = true) -> FakeFmpqMat

Returns the basis matrix of $O$.
"""
function basis_matrix(x::AlgAssAbsOrd; copy::Bool = true)
  return QQMatrix(basis_matrix(FakeFmpqMat, x, copy = false))
end

function basis_matrix(::Type{FakeFmpqMat}, x::AlgAssAbsOrd; copy::Bool = true)
  if copy
    return deepcopy(x.basis_matrix)
  else
    return x.basis_matrix
  end
end

@doc raw"""
    basis_mat_inv(O::AlgAssAbsOrd; copy::Bool = true) -> FakeFmpqMat

Returns the inverse of the basis matrix of $O$.
"""
function basis_matrix_inverse(O::AlgAssAbsOrd; copy::Bool = true)
  return QQMatrix(basis_mat_inv(FakeFmpqMat, O, copy = false))
end

function basis_mat_inv(::Type{FakeFmpqMat}, O::AlgAssAbsOrd; copy::Bool = true)
  assure_basis_mat_inv(O)
  if copy
    return deepcopy(O.basis_mat_inv)::FakeFmpqMat
  else
    return O.basis_mat_inv::FakeFmpqMat
  end
end

################################################################################
#
#  Degree
#
################################################################################

@doc raw"""
    degree(O::AlgAssAbsOrd) -> Int

Returns the dimension of the algebra containing $O$.
"""
function degree(O::AlgAssAbsOrd)
  return dim(algebra(O))
end

################################################################################
#
#  Inclusion of algebra elements
#
################################################################################

function _check_elem_in_order(a::T, O::AlgAssAbsOrd{S, T}, ::Val{short} = Val(false)) where {S, T, short}
  t = zero_matrix(QQ, 1, degree(O))
  elem_to_mat_row!(t, 1, a)
  t = FakeFmpqMat(t)
  t = t*basis_mat_inv(FakeFmpqMat, O, copy = false)
  if short
    return isone(t.den)
  else
    if !isone(t.den)
      return false, Vector{ZZRingElem}()
    else
      v = Vector{ZZRingElem}(undef, degree(O))
      for i = 1:degree(O)
        v[i] = deepcopy(t.num[1, i])
      end
      return true, v
    end
  end
end

@doc raw"""
    in(x::AbstractAssociativeAlgebraElem, O::AlgAssAbsOrd) -> Bool

Returns `true` if the algebra element $x$ is in $O$ and `false` otherwise.
"""
function in(x::T, O::AlgAssAbsOrd{S, T}) where {S, T}
  return _check_elem_in_order(x, O, Val(true))
end

################################################################################
#
#  Denominator in an order
#
################################################################################

@doc raw"""
    denominator(a::AbstractAssociativeAlgebraElem, O::AlgAssAbsOrd) -> ZZRingElem

Returns $d\in \mathbb Z$ such that $d \cdot a \in O$.
"""
function denominator(a::AbstractAssociativeAlgebraElem, O::AlgAssAbsOrd)
  t = zero_matrix(QQ, 1, degree(O))
  elem_to_mat_row!(t, 1, a)
  t = FakeFmpqMat(t)
  t = mul!(t, t, basis_mat_inv(FakeFmpqMat, O, copy = false))
  return t.den
end

################################################################################
#
#  Random elements
#
################################################################################

RandomExtensions.maketype(O::AlgAssAbsOrd, R::AbstractUnitRange) = elem_type(O)

function rand(rng::AbstractRNG,
              sp::SamplerTrivial{<:Make2{<:NCRingElem,<:AlgAssAbsOrd,<:AbstractUnitRange}})
  O, R = sp[][1:2]
  O(map(ZZRingElem, rand(rng, R, degree(O))))

end

RandomExtensions.make(O::AlgAssAbsOrd, n::IntegerUnion) =
  make(O, Integer(-n):Integer(n))

@doc raw"""
    rand(O::AlgAssAbsOrd, R::AbstractUnitRange) -> AlgAssAbsOrdElem

Returns a random element of $O$ whose coefficients lie in $R$.
"""
rand(O::AlgAssAbsOrd, R::AbstractUnitRange) = rand(Random.GLOBAL_RNG, O, R)

@doc raw"""
    rand(O::AlgAssAbsOrd, n::IntegerUnion) -> AlgAssAbsOrdElem

Returns a random element of $O$ whose coefficients are bounded by $n$.
"""
rand(O::AlgAssAbsOrd, n::ZZRingElem) = rand(Random.GLOBAL_RNG, O, n)
rand(O::AlgAssAbsOrd, n::Integer) = rand(Random.GLOBAL_RNG, O, n)
# these two methods can't be merged with a Union, because of ambiguities

rand(rng::AbstractRNG, O::AlgAssAbsOrd, n::Union{ZZRingElem, <:AbstractUnitRange}) = rand(rng, make(O, n))
rand(rng::AbstractRNG, O::AlgAssAbsOrd, n::Integer) = rand(rng, make(O, n))


################################################################################
#
#  Basis matrices from generators
#
################################################################################

function basis_matrix(A::Vector{S}, ::Type{FakeFmpqMat}) where {S <: AbstractAssociativeAlgebraElem{QQFieldElem}}
  if length(A) == 0
    return M = FakeFmpqMat(zero_matrix(ZZ, 0, 0), ZZ(1))
  end
  @assert length(A) > 0
  n = length(A)
  d = dim(parent(A[1]))

  M = zero_matrix(ZZ, n, d)

  t = ZZRingElem()

  deno = one(ZZ)
  for i in 1:n
    acoeff = coefficients(A[i], copy = false)
    for j in 1:d
      denominator!(t, acoeff[j])
      lcm!(deno, deno, t)
    end
  end

  temp_den = ZZRingElem()

  #dens = [lcm([denominator(coefficients(A[i], copy = false)[j]) for j=1:d]) for i=1:n]
  #deno = lcm(dens)

  skip_den = isone(deno)

  for i in 1:n
    acoeff = coefficients(A[i], copy = false)
    for j in 1:d
      if skip_den
        numerator!(t, acoeff[j])
        M[i, j] = t
        #M[i, j] = numerator(coefficients(A[i], copy = false)[j])
      else
        denominator!(temp_den, acoeff[j])
        divexact!(temp_den, deno, temp_den)
        numerator!(t, acoeff[j])
        mul!(t, t, temp_den)
        M[i, j] = t
      end
      #temp_den = divexact(deno, denominator(coefficients(A[i], copy = false)[j]))
      #M[i, j] = numerator(coefficients(A[i], copy = false)[j]) * temp_den
    end
  end
  return FakeFmpqMat(M, deno)
end

function basis_matrix(A::Vector{ <: AbstractAssociativeAlgebraElem{T} }) where T
  @assert length(A) > 0
  n = length(A)
  d = dim(parent(A[1]))
  K = base_ring(parent(A[1]))

  M = zero_matrix(K, n, d)

  for i = 1:n
    elem_to_mat_row!(M, i, A[i])
    #for j = 1:d
    #  M[i, j] = deepcopy(coefficients(A[i], copy = false)[j])
    #end
  end
  return M
end

function basis_matrix(A::Vector{AlgAssAbsOrdElem{S, T}}) where S where T
  @assert length(A) > 0
  n = length(A)
  d = degree(parent(A[1]))
  M = zero_matrix(ZZ, n, d)

  for i in 1:n
    el = coordinates(A[i])
    for j in 1:d
      M[i, j] = el[j]
    end
  end
  return M
end

################################################################################
#
#  Sum of orders
#
################################################################################

# Be careful!
# To be used only in the case of the construction of a maximal order!
function +(a::AlgAssAbsOrd, b::AlgAssAbsOrd)
  aB = basis_matrix(FakeFmpqMat, a, copy = false)
  bB = basis_matrix(FakeFmpqMat, b, copy = false)
  d = degree(a)
  c = sub(_hnf(vcat(bB.den*aB.num, aB.den*bB.num), :lowerleft), d + 1:2*d, 1:d)
  return Order(algebra(a), FakeFmpqMat(c, aB.den*bB.den))
end

################################################################################
#
#  Print
#
################################################################################

function show(io::IO, O::AlgAssAbsOrd)
  compact = get(io, :compact, false)
  if compact
    print(io, "Order of ")
    show(IOContext(io, :compact => true), algebra(O))
  else
    print(io, "Order of ")
    print(io, algebra(O))
    println(io, " with basis matrix ")
    print(io, basis_matrix(O))
  end
end

################################################################################
#
#  Equality
#
################################################################################

@doc raw"""
    ==(S::AlgAssAbsOrd, T::AlgAssAbsOrd) -> Bool

Returns `true` if $S$ and $T$ are equal and `false` otherwise.
"""
function ==(S::AlgAssAbsOrd, T::AlgAssAbsOrd)
  return basis_matrix(FakeFmpqMat, S, copy = false) == basis_matrix(FakeFmpqMat, T, copy = false)
end

################################################################################
#
#  Discriminant and Reduced Trace Matrix
#
################################################################################

@doc raw"""
    trred_matrix(O::AlgAssAbsOrd) -> ZZMatrix

Returns the reduced trace matrix $M$ of $O$, i. e. `M[i, j] = trred(b[i]*b[j])`,
where $b$ is a basis of $O$.
"""
function trred_matrix(O::AlgAssAbsOrd)
  if isdefined(O, :trred_matrix)
    return O.trred_matrix
  end
  A=algebra(O)
  x=O.basis_alg
  m=length(x)
  M=zero_matrix(ZZ, m, m)
  a=A()
  for i=1:m
    a = mul!(a, x[i], x[i])
    M[i,i] = ZZ(trred(a))
  end
  for i = 1:m
    for j = i+1:m
      a = mul!(a, x[i], x[j])
      b = ZZ(trred(a))
      M[i,j] = b
      M[j,i] = b
    end
  end
  O.trred_matrix = M
  return M
end

@doc raw"""
    discriminant(O::AlgAssAbsOrd) -> ZZRingElem

Returns the discriminant of $O$.
"""
function discriminant(O::AlgAssAbsOrd)
  if isdefined(O, :disc)
    return O.disc
  end
  M = trred_matrix(O)
  O.disc = det(M)
  return O.disc
end

################################################################################
#
#  p-maximal overorder
#
################################################################################

function pmaximal_overorder(O::AlgAssAbsOrd{S, T}, p::Union{ZZRingElem, Int}) where S where T
  d = discriminant(O)
  if rem(d, p^2) != 0
    return O
  end

  if p > degree(O)
    @vtime :AlgAssOrd 1 O1 = pmaximal_overorder_tr(O,p)::AlgAssAbsOrd{S, T}
    return O1
  else
    @vtime :AlgAssOrd 1 O1 = pmaximal_overorder_meataxe(O,p)::AlgAssAbsOrd{S, T}
    return O1
  end
end

function pmaximal_overorder_meataxe(O::AlgAssAbsOrd{S, T}, p::Union{ZZRingElem, Int}) where {S, T}

  extend = false
  d = discriminant(O)
  while true
    dd = ZZRingElem(1)
    @vtime :AlgAssOrd 1 max_id =_maximal_ideals(O, p*O, p, strict_containment = true)
    for m in max_id
      @vtime :AlgAssOrd 1 OO = _ring_of_multipliers_integral_ideal(m, ZZRingElem(p))
      dd = discriminant(OO)
      if d != dd
        extend = true
        O = OO
        d = dd
        break
      end
    end

    if extend
      if rem(d, p^2) != 0
        break
      end
      extend = false
      continue
    else
      break
    end

  end
  return O
end

function pmaximal_overorder_tr(O::AlgAssAbsOrd, p::IntegerUnion)
  #First, the head order by computing the pradical and its ring of multipliers
  d = discriminant(O)
  @vtime :AlgAssOrd 1 I = pradical(O, p)
  @vtime :AlgAssOrd 1 OO = _ring_of_multipliers_integral_ideal(I, ZZRingElem(p))
  dd = discriminant(OO)
  if rem(dd, p^2) != 0
    return OO
  end
  while dd!= d
    d = dd
    O = OO
    @vtime :AlgAssOrd 1 I = pradical(O,p)
    @vtime :AlgAssOrd 1 OO = _ring_of_multipliers_integral_ideal(I, ZZRingElem(p))
    dd = discriminant(OO)
    if rem(dd, p^2) != 0
      return OO
    end
  end
  #Now, we have to check the maximal ideals.

  extend = false
  @vtime :AlgAssOrd 1 max_id = _maximal_ideals(O, I, p, strict_containment = true)
  for m in max_id
    @vtime :AlgAssOrd 1 OO = _ring_of_multipliers_integral_ideal(m, ZZRingElem(p))
    dd = discriminant(OO)
    if d != dd
      extend = true
      O = OO
      d = dd
      break
    end
  end
  if extend
    if rem(dd, p^2) != 0
      return OO
    end
    extend = false
  else
    return OO
  end
  while true
    dd = ZZRingElem(1)
    @vtime :AlgAssOrd 1 max_id = _maximal_ideals(O, p*O, p, strict_containment = true)
    for m in max_id
      OO = _ring_of_multipliers_integral_ideal(m, ZZRingElem(p))
      dd = discriminant(OO)
      if d != dd
        extend = true
        O = OO
        d = dd
        break
      end
    end

    if extend
      if rem(dd, p^2) != 0
        break
      end
      extend = false
      continue
    else
      break
    end

  end
  return O
end

################################################################################
#
#  Maximal Order
#
################################################################################

@doc raw"""
    MaximalOrder(O::AlgAssAbsOrd)

Given an order $O$, this function returns a maximal order containing $O$.
"""
function MaximalOrder(O::AlgAssAbsOrd{S, T}; cached::Bool = true) where S where T
  A = algebra(O)

  if cached && has_attribute(O, :maximal_order)
    return get_attribute(O, :maximal_order)::typeof(O)
  end

  if cached && isdefined(A, :maximal_order)
    for OO::order_type(A) in A.maximal_order
      d = denominator(basis_matrix(FakeFmpqMat, O, copy = false)*basis_mat_inv(FakeFmpqMat, OO, copy = false))
      if isone(d)
        set_attribute!(O, :maximal_order, OO)
        return OO
      end
    end
  end

  # if cached == false, I also want fresh stuff in the components if it does decomposition
  OO = new_maximal_order(O, cached)

  set_attribute!(O, :maximal_order, OO)

  return OO
end

function new_maximal_order(O::AlgAssAbsOrd{S, T}, cache_in_substructures::Bool = true) where {S, T}
  A = algebra(O)

  if degree(O) >= 30 && !is_simple(A)
    OO = _maximal_order_via_decomposition(O, cache_in_substructures)
  else
    d = discriminant(O)
    @vtime :AbsNumFieldOrder fac = factor(abs(d))

    OO = O
    for (p, j) in fac
      if mod(d, p^2) != 0
        continue
      end
      OO += pmaximal_overorder(O, p)
    end
    OO.is_maximal = 1
  end

  if !isdefined(A, :maximal_order)
    A.maximal_order = [OO]
  else
    push!(A.maximal_order, OO)
  end
  return OO
end

function MaximalOrder(O::AlgAssAbsOrd{S, T}) where { S <: GroupAlgebra, T <: GroupAlgebraElem }
  A = algebra(O)

  if isdefined(A, :maximal_order)
    for OO::order_type(A) in A.maximal_order
      d = denominator(basis_matrix(FakeFmpqMat, O, copy = false)*basis_mat_inv(FakeFmpqMat, OO, copy = false))
      if isone(d)
        return OO
      end
    end
  end

  if degree(O) > 40 # group algebra is never simple
    OO = _maximal_order_via_decomposition(O)
  else
    d = discriminant(O)
    @assert degree(O) < 2^31 # squares do not overflow
    fac = factor(degree(O)) # the order of the group

    OO = O
    for (p, j) in fac
      if mod(d, p^2) != 0
        continue
      end
      OO += pmaximal_overorder(O, p)
    end

    for (p, _) in factor(ppio(discriminant(OO), ZZ(degree(O)))[2])
      OO += pmaximal_overorder(O, p)
    end

    OO.is_maximal = 1
  end

  if !isdefined(A, :maximal_order)
    A.maximal_order = [OO]
  else
    push!(A.maximal_order::Vector{order_type(A)}, OO)
  end

  return OO
end

function _denominator_of_mult_table(A::AbstractAssociativeAlgebra{QQFieldElem})
  l = one(ZZ)
  for i = 1:dim(A)
    for j = 1:dim(A)
      for k = 1:dim(A)
        l = lcm(l, denominator(multiplication_table(A, copy = false)[i, j, k]))
      end
    end
  end
  return l
end

_denominator_of_mult_table(A::GroupAlgebra{QQFieldElem}) = ZZRingElem(1)

@doc raw"""
    any_order(A::AbstractAssociativeAlgebra{QQFieldElem}) -> AlgAssAbsOrd

Returns any order of $A$.
"""
function any_order(A::AbstractAssociativeAlgebra{QQFieldElem})
  return get_attribute!(A, :any_order) do
    d = _denominator_of_mult_table(A)
    di = dim(A)
    M = vcat(zero_matrix(QQ, 1, di), d*identity_matrix(QQ, di))
    oneA = one(A)
    for i = 1:di
      M[1, i] = deepcopy(coefficients(oneA, copy = false)[i])
    end
    M = FakeFmpqMat(M)
    M = hnf!(M, :lowerleft)
    O = Order(A, sub(M, 2:di + 1, 1:di))
    return O
  end::order_type(A)
end

@doc raw"""
    MaximalOrder(A::AbstractAssociativeAlgebra{QQFieldElem}) -> AlgAssAbsOrd

Returns a maximal order of $A$.
"""
function MaximalOrder(A::AbstractAssociativeAlgebra{S}) where S
  if isdefined(A, :maximal_order)
    return first(A.maximal_order)::AlgAssAbsOrd{typeof(A), elem_type(A)}
  end

  O = any_order(A)
  OO = MaximalOrder(O)
  A.maximal_order = [OO]
  return OO
end

function maximal_order_via_decomposition(A::AbstractAssociativeAlgebra{QQFieldElem})
  if isdefined(A, :maximal_order)
    return first(A.maximal_order)::AlgAssAbsOrd{typeof(A), elem_type(A)}
  end
  fields_and_maps = __as_number_fields(A, use_maximal_order = false)
  M = zero_matrix(QQ, dim(A), dim(A))
  row = 1
  for i = 1:length(fields_and_maps)
    K = fields_and_maps[i][1]
    AtoK = fields_and_maps[i][2]
    O = maximal_order(K)
    for b in basis(O)
      a = AtoK\K(b)
      elem_to_mat_row!(M, row, a)
      row += 1
    end
  end
  FakeM = FakeFmpqMat(M)
  FakeM = hnf!(FakeM, :lowerleft)
  OO = Order(A, FakeM)
  OO.is_maximal = 1
  A.maximal_order = [OO]
  return OO
end

_debug = []

function _maximal_order_via_decomposition(O::AlgAssAbsOrd, cache_in_substructures::Bool = true)
  A = algebra(O)
  dec = decompose(A)
  Obas = basis(O)
  bas = elem_type(A)[]
  for i in 1:length(dec)
    Ai, mAi = dec[i]
    gens = [ mAi\(mAi(one(Ai)) * elem_in_algebra(b)) for b in Obas]
    OinAi = Order(Ai, gens; check = false)
    Mi = maximal_order(OinAi)
    Mibas = [ mAi(elem_in_algebra(b)) for b in basis(Mi)]
    append!(bas, Mibas)
  end
  M = Order(A, bas, isbasis = true)
  N = Order(A, hnf(basis_matrix(FakeFmpqMat, M, copy = false)))
  N.is_maximal = 1
  return N
end

# Requires that O is maximal and A = QQ^(n\times n).
# Computes a maximal order of type
#  (O ... O a^(-1))
#  (:     :   :   )
#  (O ... O a^(-1))
#  (a ... a   O   )
# for an ideal a of O.
# See Bley, Johnston "Computing generators of free modules over orders in group
# algebras", Prop. 5.1.
function _simple_maximal_order(O::AlgAssAbsOrd{S1, S2}, ::Val{with_transform} = Val(false)) where { S1 <: MatAlgebra, S2, with_transform }
  A = algebra(O)

  if !(A isa MatAlgebra)
    throw(ArgumentError("Order must be an order in a matrix algebra"))
  end

  n = degree(A)

  # Build a matrix with the first rows of basis elements of O
  M = zero_matrix(QQ, dim(A), n)
  for i = 1:dim(A)
    for j = 1:n
      M[i, j] = deepcopy(matrix(elem_in_algebra(basis(O, copy = false)[i], copy = false), copy = false)[1, j])
    end
  end
  M = FakeFmpqMat(M)
  M = hnf!(M, :upperright)
  M = QQMatrix(sub(M, 1:n, 1:n))

  # Compute M * O * M^-1
  iM = inv(M)
  bb = Vector{elem_type(A)}()
  for i = 1:degree(O)
    push!(bb, M*elem_in_algebra(basis(O, copy = false)[i], copy = false)*iM)
  end

  simpleOrder = Order(A, bb)
  simpleOrder.isnice = true

  @assert basis_matrix(FakeFmpqMat, simpleOrder) == FakeFmpqMat(identity_matrix(QQ, n^2))

  if with_transform
    return simpleOrder, A(M)
  else
    return simpleOrder
  end
end

function is_simple(O::AlgAssAbsOrd)
  return O.is_simple
end

@doc raw"""
    nice_order(O::AlgAssAbsOrd) -> AlgAssAbsOrd, AlgElem

Given a maximal order `O` in a full matrix algebra over the rationals, return a
nice maximal order `R` and element `a` such that `a O a^-1 = R`.
"""
function nice_order(O::AlgAssAbsOrd{S, T}) where {S, T}
  if isdefined(O, :nice_order)
    return O.nice_order::Tuple{typeof(O), T}
  else
    sO, A = _simple_maximal_order(O, Val(true))
    O.nice_order = sO, A
    return sO, A
  end
end

################################################################################
#
#  Conductor
#
################################################################################

@doc raw"""
    conductor(R::AlgAssAbsOrd, S::AlgAssAbsOrd, action::Symbol) -> AlgAssAbsOrdIdl

Returns the ideal $\{ x \in R \mid xS \subseteq R \}$ if `action == :right` and
$\{ x \in R \mid Sx \subseteq R \}$ if `action == :left`.
It is assumed that $R \subseteq S$.
"""
function conductor(R::AlgAssAbsOrd, S::AlgAssAbsOrd, action::Symbol = :left)
  n = degree(R)
  t = basis_matrix(FakeFmpqMat, R, copy = false)*basis_mat_inv(FakeFmpqMat, S, copy = false)
  @assert isone(t.den)
  basis_mat_R_in_S_inv_num, d = pseudo_inv(t.num)
  M = zero_matrix(ZZ, n^2, n)
  B = basis(S, copy = false)

  NN = transpose(representation_matrix(B[1], action)*basis_mat_R_in_S_inv_num)
  NNhnf = hnf(NN)
  H = add_to_hnf_from_matrix_stream(NNhnf, (transpose(representation_matrix(B[k], action) * basis_mat_R_in_S_inv_num) for k in 2:n))
  #for k in 1:n
  #  a = B[k]
  #  N = representation_matrix(a, action)*basis_mat_R_in_S_inv_num
  #  for i in 1:n
  #    for j in 1:n
  #      M[(k - 1)*n + i, j] = N[j, i]
  #    end
  #  end
  #end
  #HH = sub(hnf(M), 1:n, 1:n)
  #@assert H == HH
  Hinv = inv(FakeFmpqMat(transpose(H)))
  Hinv = Hinv*basis_mat_R_in_S_inv_num*basis_matrix(FakeFmpqMat, R, copy = false)
  if action == :left
    return ideal(algebra(R), R, Hinv; side=:right)
  else
    return ideal(algebra(R), R, Hinv; side=:left)
  end
end

################################################################################
#
#  Units of quotients
#
################################################################################

# Computes a generating system of U in O, where U is a set of representatives of
# the image of the projection map \pi:O^\times -> (O/g*O)^\times.
# Assumes that O is a maximal order in Mat_{n\times n}(QQ).
# See Bley, Johnson: "Computing generators of free modules over orders in
# group algebras", section 6.
function enum_units(O::AlgAssAbsOrd{S, T}, g::ZZRingElem) where { S <: MatAlgebra, T }
  A = algebra(O)
  @assert degree(A)^2 == dim(A)

  n = degree(A)

  L = _simple_maximal_order(O)
  a = basis_matrix(FakeFmpqMat, L, copy = false)[dim(A) - 1, dim(A) - 1]
  ai = basis_matrix(FakeFmpqMat, L, copy = false)[n, n]

  result = Vector{elem_type(L)}()
  n1 = n - 1
  # n \nmid i, j or n \mid i, j
  for i = 1:n1
    for j = 1:n1
      if j == i
        continue
      end
      E = identity_matrix(QQ, n)
      E[i, j] = deepcopy(g)
      push!(result, L(A(E)))
    end
  end

  # n \nmid i and n \mid j
  for i = 1:n1
    E = identity_matrix(QQ, n)
    E[i, n] = deepcopy(a)
    push!(result, L(A(E)))
  end

  # n \mid i and n \nmid j
  for j = 1:n1
    E = identity_matrix(QQ, n)
    E[n, j] = deepcopy(ai)
    push!(result, L(A(E)))
  end

  E = identity_matrix(QQ, n)
  E[1, 1] = ZZRingElem(-1)
  push!(result, L(A(E)))
  return result
end

################################################################################
#
#  Trace dual ideal
#
################################################################################

function trace_dual(R::AlgAssAbsOrd)
  t = inv(FakeFmpqMat(trred_matrix(R)))*basis_matrix(FakeFmpqMat, R, copy = false)
  return ideal(algebra(R), R, t)
end

################################################################################
#
#  "All" maximal orders
#
################################################################################

# Only works for algebras fulfilling the Eichler condition.
# This is trivial for algebras over QQ, as there is always just one equivalence
# class with respect to conjugation.
representatives_of_maximal_orders(A::StructureConstantAlgebra{QQFieldElem}) = representatives_of_maximal_orders(maximal_order(A))

function representatives_of_maximal_orders(O::AlgAssAbsOrd)
  A = algebra(O)
  @assert is_simple(A)
  @assert is_eichler(A)
  @assert is_maximal(O)
  return typeof(O)[ O ]
end

################################################################################
#
#  Subset test
#
################################################################################

function is_subset(R::AlgAssAbsOrd, S::AlgAssAbsOrd)
  B = basis_matrix(FakeFmpqMat, R, copy = false) * basis_mat_inv(FakeFmpqMat, S, copy = false)
  return is_one(denominator(B))
end
