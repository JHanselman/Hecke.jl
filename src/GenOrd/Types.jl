@attributes mutable struct GenOrd{S, T} <: Ring
  F::S
  R::T
  trans#::dense_matrix_type(elem_type(S))
  itrans#::dense_matrix_type(elem_type(S))
  is_standard::Bool

  function GenOrd(R::AbstractAlgebra.Ring, F::AbstractAlgebra.Field, empty::Bool = false; check::Bool = true)
    #empty allows to create an Order that is none:
    # Z[x]/3x+1 is no order. This will be "fixed" by using any_order, but
    #the initial shell needs to be empty (illegal)
    r = new{typeof(F), typeof(R)}()
    r.F = F
    r.R = R
    r.is_standard = true
    empty && return r
    Qt = base_field(F)
    d = reduce(lcm, map(x->denominator(x, R), coefficients(defining_polynomial(F))))
    f = map_coefficients(x->numerator(Qt(d)*x, R), defining_polynomial(F), cached = false)
    if !is_monic(f) #need Lenstra Order
      d = degree(F)
      M = zero_matrix(Qt, d, d)
      M[1, 1] = one(Qt)
      for i in 2:d
        for j in i:-1:1
          M[i, j] = coeff(f, d - (i - j))
        end
      end
      O = GenOrd(r, M, one(Qt), check = check)
      return O
    end
    return r
  end

  function GenOrd(O::GenOrd, T::MatElem, d::RingElem; check::Bool = true)
    F = base_field(O.F)
    T = map_entries(F, T)
    T = divexact(T, base_ring(T)(d))
    Ti = inv(T)
    r = GenOrd(O.R, O.F, true)
    r.is_standard = false
    if isdefined(O, :trans)
      r.trans = T*O.trans
      r.itrans = O.itrans*Ti
    else
      r.trans = T
      r.itrans = Ti
    end
    check && map(representation_matrix, basis(r))
    return r
  end
end

mutable struct GenOrdElem{S, T} <: RingElem
  parent::GenOrd
  data::S
  coord::Vector{T}

  function GenOrdElem(O::GenOrd{S, T}, f::FieldElem, check::Bool = false) where {S, T}
    @assert parent(f) === O.F
    if check && !is_unit(integral_split(f, O)[2])
      error("element not in order")
    end
    r = new{typeof(f), elem_type(T)}()
    r.parent = O
    r.data = f
    return r
  end
end

################################################################################
#
#  Ideals
#
################################################################################

@attributes mutable struct GenOrdIdl{S, T}
  order::GenOrd{S, T}
  basis#::Vector{elem_type(GenOrd{S, T}}
  basis_matrix#dense_matrix_type(T)
  basis_mat_inv#dense_matrix_type(S)
  norm
  minimum
  is_prime::Int            # 0: don't know
                           # 1 known to be prime
                           # 2 known to be not prime
  is_zero::Int             # as above
  is_principal::Int        # as above

  gen_one::RingElem
  gen_two::GenOrdElem

  princ_gen::GenOrdElem
  prim_elem::GenOrdElem
  min_poly_prim_elem
  basis_in_prim
  phi

  splitting_type::Tuple{Int, Int}
                         #ordered as ramification index, inertia degree


  function GenOrdIdl(O::GenOrd{S, T}) where {S, T}
    r = new{S, T}()
    r.order = O
    r.is_prime = 0
    r.is_zero = 0
    r.is_principal = 0
    r.splitting_type = (-1, -1)
    return r
  end

  function GenOrdIdl(O::GenOrd, M::MatElem)
    @assert base_ring(M) === coefficient_ring(O)
    # create ideal of O with basis_matrix M
    r = GenOrdIdl(O)
    r.basis_matrix = M
    return r
  end

  function GenOrdIdl(O::GenOrd, x::GenOrdElem)
    # create ideal of O generated by x
    @assert parent(x) === O
    r = GenOrdIdl(O)
    r.princ_gen = x
    r.is_principal = 1

    if iszero(x)
       r.is_zero = 1
    end

    r.norm = norm(x)
    r.gen_one = r.norm
    r.gen_two = x
    return r
  end

  function GenOrdIdl(O::GenOrd, x::RingElem)
    return GenOrdIdl(O, O(x))
  end

  function GenOrdIdl(O::GenOrd, T::Vector{<:GenOrdElem})
    @assert all(x -> parent(x) === O, T)
    # One should do this block by block instead of the big matrix
    V = hnf(reduce(vcat, [representation_matrix(O) for x in T]), :lowerleft)
    d = ncols(V)
    n = length(T)
    return GenOrdIdl(O, V[((n - 1)*d + 1):(n*d), :])
  end

  function GenOrdIdl(O::GenOrd, p::RingElem, a::GenOrdElem)
    r = GenOrdIdl(O)
    r.gen_one = p
    r.gen_two = a
    return r
  end
end

@attributes mutable struct GenOrdFracIdl{S, T}
  order::GenOrd{S, T}
  num::GenOrdIdl{S, T}
  den::RingElem
  norm::RingElem
  basis_matrix#::FakeFracFldMat
  basis_mat_inv#::FakeFracFldMat

  function GenOrdFracIdl(O::GenOrd{S, T}) where {S, T}
    z = new{S, T}()
    z.order = O
    return z
  end

  function GenOrdFracIdl(a::GenOrdIdl{S, T}, b::RingElem) where {S, T}
    z = new{S, T}()
    O = order(a)
    z.order = O
    if isa(b, KInftyElem)
      b = O.R(Hecke.AbstractAlgebra.MPolyFactor.make_monic(numerator(b))//denominator(b))
    elseif isa(b, PolyRingElem)
      b = Hecke.AbstractAlgebra.MPolyFactor.make_monic(b)
    end
    z.num = a
    z.den = b
    return z
  end

   function GenOrdFracIdl(a::GenOrdIdl{S, T}) where {S, T}
    z = new{S, T}()
    O = order(a)
    z.order = order(a)
    z.num = a
    z.den = O.R(1)
    return z
  end


  function GenOrdFracIdl(O::GenOrd{S, T}, a::MatElem) where {S, T}
    z = new{S, T}()
    z.order = O
    z.basis_matrix = a
    return z
  end
end
