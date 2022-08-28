using Hecke

export Divisor

export finite_maximal_order, infinite_maximal_order, function_field, field_of_fractions, divisor, ideals

mutable struct Divisor
  function_field::AbstractAlgebra.Generic.FunctionField
  finite_ideal::GenOrdFracIdl
  infinite_ideal::GenOrdFracIdl

  function Divisor(I::GenOrdFracIdl, J::GenOrdFracIdl)
    r = new()
    
    O = order(I)
    Oinf = order(J)
    K = function_field(O)
    
    @req K == function_field(Oinf) "Ideals need to belong to orders of the same function field."
    @req isa(base_ring(O), PolyRing) "First ideal needs to be an ideal over the finite order"
    @req isa(base_ring(Oinf), KInftyRing) "Second ideal needs to be an ideal over the infinite order"
    
    r.function_field = K
    r.finite_ideal = I
    r.infinite_ideal = J
    
    return r
  end

end

@attributes AbstractAlgebra.Generic.FunctionField

function divisor(I::GenOrdIdl, J::GenOrdIdl)
  return Divisor(GenOrdFracIdl(I), GenOrdFracIdl(J))
end

function divisor(I::GenOrdIdl)
  O = order(I)
  F = function_field(O)
  Ofin = finite_maximal_order(F)
  Oinf = infinite_maximal_order(F)
  if O == Ofin
    return divisor(I, ideal(Oinf, one(Oinf)))
  elseif O == Oinf
    return divisor(ideal(Ofin, one(Ofin)), I)
  else
    error("There is a bug in divisor")
  end
end

function function_field(D::Divisor)
  return D.function_field
end

function ideals(D)
  return D.finite_ideal, D.infinite_ideal
end

function field_of_fractions(O::GenOrd)
  return O.F
end

function function_field(O::GenOrd)
  return O.F
end

function constant_field(K::AbstractAlgebra.Generic.FunctionField)
  return base_ring(base_ring(K))
end

function finite_maximal_order(K::AbstractAlgebra.Generic.FunctionField)
  get_attribute!(K, :finite_maximal_order) do
    return _finite_maximal_order(K)
  end
end

function _finite_maximal_order(K::AbstractAlgebra.Generic.FunctionField)
  kx = parent(numerator(gen(base_ring(K))))
  return integral_closure(kx, K)
end

function infinite_maximal_order(K::AbstractAlgebra.Generic.FunctionField)
  get_attribute!(K, :infinite_maximal_order) do
    return _infinite_maximal_order(K)
  end
end

function _infinite_maximal_order(K::AbstractAlgebra.Generic.FunctionField)
  R = Localization(base_ring(K),degree)
  Oinf = integral_closure(R, K)
  return Oinf
end

function Base.:+(D1::Divisor, D2::Divisor)
  D1_fin, D1_inf = ideals(D1)
  D2_fin, D2_inf = ideals(D2)
  return Divisor(D1_fin * D2_fin, D1_inf * D2_inf)
end

function Base.:-(D1::Divisor, D2::Divisor)
  D1_fin, D1_inf = ideals(D1)
  D2_fin, D2_inf = ideals(D2)
  return Divisor(D1_fin // D2_fin, D1_inf // D2_inf)
end

function Base.:*(n::Int, D1::Divisor)
  D1_fin, D1_inf = ideals(D1)
  return Divisor(D1_fin^n, D1_inf^n)
end

Base.:*(D::Divisor, n::Int) = n * D

function RiemannRochSpace(D::Divisor)
  I_fin, I_inf = ideals(D)
  J_fin = colon(GenOrdIdl(O, one(O)), D_fin)
  J_inf = colon(GenOrdIdl(O, one(O)), D_inf)
  
  B_fin = basis_matrix(J_fin)
  B_inf = basis_matrix(J_inf)
  
  M = solve(J_inf, J_fin)
  
  
end


